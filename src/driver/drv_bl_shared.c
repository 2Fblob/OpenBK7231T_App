// Internal code ONLY

#include <stdlib.h>   // atof, abs
#include <stdio.h>    // snprintf
#include <string.h>   // memset, strlen

// Charger C mapping constants
#define CHARGER_MIN_PWM   10      // lowest useful duty for the supply
#define CHARGER_MAX_PWM  100

// Set to 32 slots (8-hour circular buffer to match the new 8-hour graph)
static int consumption_matrix [32] = {0}; 
static int export_matrix[32] = {0};
static int net_matrix[32] = {0};

static int old_export_energy = 0;
static int old_real_consumption = 0;
static int net_energy_equivalent = 0;
static int old_output = 0;
static int update_number = 0;
int adjust_net_energy = 50;
int save_to_flash_flag = 0;
int solar_available = 0;
static int estimated_energy_start = 0;
static int last_run_calc = 0;
int output_index = 0;

int estimated_energy_period = 0;

// Initialize temp variables
int total_net_consumption = 0;
int total_net_export = 0;
int total_consumption = 0;
int total_export = 0;
int current_hour_consumption = 0;

int minutes_since_midnight = 0;
int check_interval = 0;
int check_time_estimate = 59;

#define dump_load_relay_number 6
#define charger_c_ip 21
#define net_metering_period 15

// The array where we store the power state for each of these devices
int last_dump_load_relay[dump_load_relay_number] = {2, 2, 2, 2, 2, 2};
static int dump_load_relay[dump_load_relay_number] = {0};
static int dump_load_relay_timer[dump_load_relay_number] = {0};
static int dump_load_relay_ip[dump_load_relay_number] = {23, 22, 29, 24, 27, charger_c_ip};
int cmd_ctrl = dump_load_relay_number;

static int last_matrix_index = -1; 
int charger_c_auto = 1;

#include "drv_bl_shared.h"

#include "../new_cfg.h"
#include "../new_pins.h"
#include "../cJSON/cJSON.h"
#include "../hal/hal_flashVars.h"
#include "../logging/logging.h"
#include "../mqtt/new_mqtt.h"
#include "../ota/ota.h"
#include "drv_local.h"
#include "drv_ntp.h"
#include "drv_public.h"
#include "drv_uart.h"
#include "../cmnds/cmd_public.h" //for enum EventCode
#include <math.h>
#include <time.h>

int stat_updatesSkipped = 0;
int stat_updatesSent = 0;
char ip[3];

static byte savetoflash = 0;
static byte min_reset = 0;
static float net_energy = 0;
static float real_export = 0;
static float real_consumption = 0;

// Variables for the solar dump load timer
static byte time_hour_reset = 0;
static byte time_min_reset = 0;
static byte old_time = 0;
#define dump_load_hysteresis 1 
#define max_export -3300

int lastsync = 0;                
byte check_time = 0;                    
byte check_hour = 0;                    
              
const char UNIT_WH[] = "Wh";
struct {
    energySensorNames_t names;
    byte rounding_decimals;
    float changeSendThreshold;
    double lastReading; 
    double lastSentValue; 
    int noChangeFrame; 
} sensors[OBK__NUM_SENSORS] = { 
    {{"voltage",        "V",    "Voltage",                  "voltage",                  "0", },  0,  1,   },            
    {{"current",        "A",    "Current",                  "current",                  "1", },  2,  0.01,},            
    {{"power",          "W",    "Power",                    "power",                    "2", },  0,  10,  },            
    {{"apparent_power", "VA",   "Apparent Power",           "power_apparent",           "9", },  0,  10,  },             
    {{"reactive_power", "Wh",   "Energy Balance",           "power_reactive",           "10",},  0,  1,   },            
    {{"power_factor",   "",     "Power Factor",             "power_factor",             "11",},  1,  0.1, },            
    {{"energy",         UNIT_WH,"Total Consumption",        "energycounter",            "3", },  2,  0.1, },            
    {{"energy",         UNIT_WH,"Total Generation",         "energycounter_generation", "14",},  2,  0.1, },            
    {{"energy",         UNIT_WH,"Energy Last Hour",         "energycounter_last_hour",  "4", },  2,  0.1, },            
    {{"energy",         UNIT_WH,"Energy Today",             "energycounter_today",      "7", },  2,  0.1, },            
    {{"energy",         UNIT_WH,"Energy Yesterday",         "energycounter_yesterday",  "6", },  2,  0.1, },            
    {{"energy",         UNIT_WH,"Energy 2 Days Ago",        "energycounter_2_days_ago", "12",},  2,  0.1, },            
    {{"energy",         UNIT_WH,"Energy 3 Days Ago",        "energycounter_3_days_ago", "13",},  2,  0.1, },            
    {{"timestamp",      "",     "Energy Clear Date",        "energycounter_clear_date", "8", },  0,  86400,},            
}; 

float lastReadingFrequency = NAN;
portTickType energyCounterStamp;

bool energyCounterStatsEnable = false;
int energyCounterSampleCount = 60;
int energyCounterSampleInterval = 60;
float *energyCounterMinutes = NULL;
portTickType energyCounterMinutesStamp;
long energyCounterMinutesIndex;
bool energyCounterStatsJSONEnable = false;

int actual_mday = -1;
float lastSavedEnergyCounterValue = 0.0f;
float lastSavedGenerationCounterValue = 0.0f;
float changeSavedThresholdEnergy = 500.0f;
long ConsumptionSaveCounter = 0;
portTickType lastConsumptionSaveStamp;
time_t ConsumptionResetTime = 0;

int changeSendAlwaysFrames = 60;
int changeDoNotSendMinFrames = 5;

void BL09XX_AppendInformationToHTTPIndexPage(http_request_t *request)
{
    // Dashboard migrated to standalone JSON architecture on /dash
}

void BL09XX_SaveEmeteringStatistics()
{
    ENERGY_METERING_DATA data;
    memset(&data, 0, sizeof(ENERGY_METERING_DATA));

    data.TotalGeneration = sensors[OBK_GENERATION_TOTAL].lastReading;
    data.TotalConsumption = sensors[OBK_CONSUMPTION_TOTAL].lastReading;
    data.TodayConsumpion = sensors[OBK_CONSUMPTION_TODAY].lastReading;
    data.YesterdayConsumption = sensors[OBK_CONSUMPTION_YESTERDAY].lastReading;
    data.actual_mday = actual_mday;
    data.ConsumptionHistory[0] = sensors[OBK_CONSUMPTION_2_DAYS_AGO].lastReading;
    data.ConsumptionHistory[1] = sensors[OBK_CONSUMPTION_3_DAYS_AGO].lastReading;
    data.ConsumptionResetTime = ConsumptionResetTime;
    ConsumptionSaveCounter++;
    data.save_counter = ConsumptionSaveCounter;

    HAL_SetEnergyMeterStatus(&data);
}

commandResult_t BL09XX_ResetEnergyCounter(const void *context, const char *cmd, const char *args, int cmdFlags)
{
    float value;
    int i;

    if(args==0||*args==0) 
    {
        sensors[OBK_GENERATION_TOTAL].lastReading = 0.0;
        sensors[OBK_CONSUMPTION_TOTAL].lastReading = 0.0;
        energyCounterStamp = xTaskGetTickCount();
        if (energyCounterStatsEnable == true)
        {
            if (energyCounterMinutes != NULL)
            {
                for(i = 0; i < energyCounterSampleCount; i++)
                {
                    energyCounterMinutes[i] = 0.0;
                }
            }
            energyCounterMinutesStamp = xTaskGetTickCount();
            energyCounterMinutesIndex = 0;
        }
        for(i = OBK_CONSUMPTION__DAILY_FIRST; i <= OBK_CONSUMPTION__DAILY_LAST; i++)
        {
            sensors[i].lastReading = 0.0;
        }
    } else {
        value = atof(args);
        sensors[OBK_CONSUMPTION_TOTAL].lastReading = value;
        energyCounterStamp = xTaskGetTickCount();
    }
    ConsumptionResetTime = (time_t)NTP_GetCurrentTime();
#if WINDOWS
#elif PLATFORM_BL602
#elif PLATFORM_W600 || PLATFORM_W800
#elif PLATFORM_XR809
#elif PLATFORM_BK7231N || PLATFORM_BK7231T
    if (ota_progress()==-1)
#endif
    { 
        BL09XX_SaveEmeteringStatistics();
        lastConsumptionSaveStamp = xTaskGetTickCount();
    }
    return CMD_RES_OK;
}

commandResult_t BL09XX_SetDumpLoad(const void *context, const char *cmd, const char *args, int cmdFlags)
{
    if (charger_c_auto == 1) return CMD_RES_OK; 
    
    if(args && *args) {
        dump_load_relay[5] = atoi(args);
        
        char dgr_cmd[64];
        snprintf(dgr_cmd, sizeof(dgr_cmd), "DGR_SendDimmer solar_dump %d", dump_load_relay[5]);
        CMD_ExecuteCommand(dgr_cmd, 0);

        char fallback_cmd[64];
        snprintf(fallback_cmd, sizeof(fallback_cmd), "SendGet http://192.168.8.%d/cm?cmnd=Channel3%%20%d", charger_c_ip, dump_load_relay[5]);
        CMD_ExecuteCommand(fallback_cmd, 0);
    }
    return CMD_RES_OK;
}

commandResult_t BL09XX_ToggleAuto(const void *context, const char *cmd, const char *args, int cmdFlags)
{
    charger_c_auto = !charger_c_auto;
    return CMD_RES_OK;
}

commandResult_t BL09XX_SetupEnergyStatistic(const void *context, const char *cmd, const char *args, int cmdFlags)
{
    int enable, sample_time, sample_count, json_enable;
    Tokenizer_TokenizeString(args,0);
    if (Tokenizer_CheckArgsCountAndPrintWarning(cmd, 3)) {
        return CMD_RES_NOT_ENOUGH_ARGUMENTS;
    }

    enable = Tokenizer_GetArgInteger(0);
    sample_time = Tokenizer_GetArgInteger(1);
    sample_count = Tokenizer_GetArgInteger(2);
    if (Tokenizer_GetArgsCount() >= 4)
        json_enable = Tokenizer_GetArgInteger(3);
    else
        json_enable = 0;

    if (sample_time <10) sample_time = 10;
    if (sample_time >900) sample_time = 900;
    if (sample_count < 10) sample_count = 10;
    if (sample_count > 180) sample_count = 180;   

    if (enable != 0)
    {
        energyCounterStatsEnable = true;
        if (energyCounterSampleCount != sample_count)
        {
            if (energyCounterMinutes != NULL)
                os_free(energyCounterMinutes);
            energyCounterMinutes = NULL;
            energyCounterSampleCount = sample_count;
        }
        if (energyCounterSampleInterval != sample_time)
        {
            energyCounterSampleInterval = sample_time;
            if (energyCounterMinutes != NULL)
                memset(energyCounterMinutes, 0, energyCounterSampleCount*sizeof(float));
        }
        if (energyCounterMinutes == NULL)
        {
            energyCounterMinutes = (float*)os_malloc(sample_count*sizeof(float));
            if (energyCounterMinutes != NULL)
            {
                memset(energyCounterMinutes, 0, energyCounterSampleCount*sizeof(float));
            }
        }
        energyCounterMinutesStamp = xTaskGetTickCount();
        energyCounterMinutesIndex = 0;
    } else {
        energyCounterStatsEnable = false;
        if (energyCounterMinutes != NULL)
        {
            os_free(energyCounterMinutes);
            energyCounterMinutes = NULL;
        }
        energyCounterSampleCount = sample_count;
        energyCounterSampleInterval = sample_time;
    }

    energyCounterStatsJSONEnable = (json_enable != 0) ? true : false; 
    return CMD_RES_OK;
}

commandResult_t BL09XX_VCPPublishIntervals(const void *context, const char *cmd, const char *args, int cmdFlags)
{
    Tokenizer_TokenizeString(args, 0);
    if (Tokenizer_CheckArgsCountAndPrintWarning(cmd, 2)) { return CMD_RES_NOT_ENOUGH_ARGUMENTS; }
    changeDoNotSendMinFrames = Tokenizer_GetArgInteger(0);
    changeSendAlwaysFrames = Tokenizer_GetArgInteger(1);
    return CMD_RES_OK;
}

commandResult_t BL09XX_VCPPrecision(const void *context, const char *cmd, const char *args, int cmdFlags)
{
    int i;
    Tokenizer_TokenizeString(args, 0);
    if (Tokenizer_CheckArgsCountAndPrintWarning(cmd, 1)) { return CMD_RES_NOT_ENOUGH_ARGUMENTS; }

    for (i = 0; i < Tokenizer_GetArgsCount(); i++) {
        int val = Tokenizer_GetArgInteger(i);
        switch(i) {
        case 0: sensors[OBK_VOLTAGE].rounding_decimals = val; break;
        case 1: sensors[OBK_CURRENT].rounding_decimals = val; break;
        case 2: 
            sensors[OBK_POWER].rounding_decimals = val;
            sensors[OBK_POWER_APPARENT].rounding_decimals = val;
            sensors[OBK_POWER_REACTIVE].rounding_decimals = val;
            break;
        case 3: 
            for (int j = OBK_CONSUMPTION__DAILY_FIRST; j <= OBK_CONSUMPTION__DAILY_LAST; j++) {
                sensors[j].rounding_decimals = val;
            };
        };
    }
    return CMD_RES_OK;
}

commandResult_t BL09XX_VCPPublishThreshold(const void *context, const char *cmd, const char *args, int cmdFlags)
{
    Tokenizer_TokenizeString(args, 0);
    if (Tokenizer_CheckArgsCountAndPrintWarning(cmd, 3)) { return CMD_RES_NOT_ENOUGH_ARGUMENTS; }

    sensors[OBK_VOLTAGE].changeSendThreshold = Tokenizer_GetArgFloat(0);
    sensors[OBK_CURRENT].changeSendThreshold = Tokenizer_GetArgFloat(1);
    sensors[OBK_POWER].changeSendThreshold = Tokenizer_GetArgFloat(2);
    sensors[OBK_POWER_APPARENT].changeSendThreshold = Tokenizer_GetArgFloat(2);
    sensors[OBK_POWER_REACTIVE].changeSendThreshold = Tokenizer_GetArgFloat(2);

    if (Tokenizer_GetArgsCount() >= 4) {
        for (int i = OBK_CONSUMPTION_LAST_HOUR; i <= OBK_CONSUMPTION__DAILY_LAST; i++) {
            sensors[i].changeSendThreshold = Tokenizer_GetArgFloat(3);
        }
    }
    return CMD_RES_OK;
}

commandResult_t BL09XX_SetupConsumptionThreshold(const void *context, const char *cmd, const char *args, int cmdFlags)
{
    float threshold;
    Tokenizer_TokenizeString(args,0);
    if (Tokenizer_CheckArgsCountAndPrintWarning(cmd, 1)) { return CMD_RES_NOT_ENOUGH_ARGUMENTS; }
    
    threshold = atof(Tokenizer_GetArg(0)); 
    if (threshold<1.0f) threshold = 1.0f;
    if (threshold>1000.0f) threshold = 1000.0f;
    
    changeSavedThresholdEnergy = threshold;
    addLogAdv(LOG_INFO, LOG_FEATURE_ENERGYMETER, "ConsumptionThreshold: %1.1f", changeSavedThresholdEnergy);
    return CMD_RES_OK;
}

bool Channel_AreAllRelaysOpen() {
    int i, role, ch;
    for (i = 0; i < PLATFORM_GPIO_MAX; i++) {
        role = g_cfg.pins.roles[i];
        ch = g_cfg.pins.channels[i];
        if (role == IOR_Relay) {
            if (CHANNEL_Get(ch)) { return false; }
        }
        if (role == IOR_Relay_n) {
            if (CHANNEL_Get(ch)==false) { return false; }
        }
        if (role == IOR_BridgeForward) {
            if (CHANNEL_Get(ch)) { return false; }
        }
    }
    return true;
}

float BL_ChangeEnergyUnitIfNeeded(float Wh) {
    if (CFG_HasFlag(OBK_FLAG_MQTT_ENERGY_IN_KWH)) { return Wh * 0.001f; }
    return Wh;
}

void BL_ProcessUpdate(float voltage, float current, float power, float frequency, float energyWh) {
    int i;
    int xPassedTicks;
    float energy_counter_data = 0;
              
    cJSON* root;
    cJSON* stats;
    char *msg;
    portTickType interval;
    time_t ntpTime;
    struct tm *ltm;
    char datetime[64];
    float diff;

    if (CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE) && NTP_IsTimeSynced())
    {                                         
        check_time = NTP_GetMinute();
        check_hour = NTP_GetHour();

        // ------------------------------------------------------------------------------------------------------
        // THE 15-MINUTE RESET & CIRCULAR MATRIX LOGIC 
        // ------------------------------------------------------------------------------------------------------
        int minutes_since_midnight_tracker = (check_hour * 60) + check_time;
        int interval_of_day_tracker = minutes_since_midnight_tracker / 15;
        
        int current_matrix_index = interval_of_day_tracker % 32; 

        if (last_matrix_index == -1) {
            last_matrix_index = current_matrix_index;
        }

        if (current_matrix_index != last_matrix_index) {
            
            consumption_matrix[last_matrix_index] = (int)real_consumption;
            export_matrix[last_matrix_index] = (int)real_export;
            net_matrix[last_matrix_index] = (int)real_consumption - (int)real_export;

            real_export = 0;
            real_consumption = 0;
            net_energy = 0;
            energyCounterMinutesIndex = 0;
            lastsync = 0; 
            
            consumption_matrix[current_matrix_index] = 0;
            export_matrix[current_matrix_index] = 0;
            net_matrix[current_matrix_index] = 0;

            last_matrix_index = current_matrix_index;
            savetoflash = 1;
        }

        if (!(check_time == old_time))
        {
            min_reset = 1;
            old_time = check_time;
            lastsync++;
        }
                                                         
        net_energy = (real_consumption - real_export);                               

        // ======================================================================================================
        // THE 30-SECOND CALCULATION LOOP (Target -20Wh, Asymmetric Control, Split Red/Green rendering)
        // ======================================================================================================
        static portTickType last_control_tick = 0;
        portTickType current_tick = xTaskGetTickCount();
        
        if ((current_tick - last_control_tick) >= (30000 / portTICK_PERIOD_MS) || last_control_tick == 0) 
        {
            last_control_tick = current_tick;
            
            int min_in_block = check_time % 15; 
            int check_time_estimate_mins = 15 - min_in_block; 
            if (check_time_estimate_mins <= 0) check_time_estimate_mins = 1;
            
            // 1. Predict total Wh accumulated by the end of the 15-minute period
            estimated_energy_period = (int)net_energy + ((int)sensors[OBK_POWER].lastReading * check_time_estimate_mins) / 60;
            
            // 2. Extrapolate immediate equivalent energy
            if (min_in_block > 0) {
                net_energy_equivalent = (int)((float)net_energy * (15.0f / min_in_block));                                               
            } else {
                net_energy_equivalent = (int)net_energy; 
            }

            // 3. Update Base Solar State
            if (net_energy < -30.0f) {
                solar_available = 1;
            } else if (net_energy > 10.0f) {
                solar_available = 0;
            }

            // ====================================================================
            // ISOLATED LOGIC BLOCK (ONLY RUNS IN AUTO MODE)
            // ====================================================================
            if (charger_c_auto == 1) {
                static int solar_excess = 0; 
                static int persistent_state = 0; // Tracks 0, 5, or 18+

                if (solar_available == 0) {
                    if (net_energy < -10.0f) {
                        persistent_state = 0;
                    } else if (net_energy > 5.0f) {
                        persistent_state = 5;
                    }
                    solar_excess = 0; // Zero the accumulator for when solar returns
                } 
                else {
                    // solar_available == 1 -> Charger Floor is 18
                    if (net_energy > -20.0f) {
                        // Instant safety drop if we drift above the target threshold
                        solar_excess = 0; 
                    } else {
                        // Calculate Watts needed to hit the -20Wh target
                        int excess_wh = abs(estimated_energy_period + 20); 
                        int error_w = (excess_wh * 60) / check_time_estimate_mins; 
                        
                        // Increase by 50% of the required adjustment in PWM units (100% = 1000W)
                        int pwm_step = (error_w / 10) / 2;
                        if (pwm_step < 1) pwm_step = 1; // Enforce movement
                        
                        solar_excess += pwm_step;
                    }
                    
                    // Enforce absolute constraints
                    if (solar_excess > 82) solar_excess = 82;
                    if (solar_excess < 0) solar_excess = 0;
                    
                    persistent_state = 18 + solar_excess;
                }
                
                dump_load_relay[5] = persistent_state;
            } // END OF AUTO MODE BLOCK

            // ====================================================================
            // UNCONDITIONAL SEND: Runs every 30-seconds regardless of Auto/Manual
            // ====================================================================
            char dgr_cmd[64];
            snprintf(dgr_cmd, sizeof(dgr_cmd), "DGR_SendDimmer solar_dump %d", dump_load_relay[5]);
            CMD_ExecuteCommand(dgr_cmd, 0);

            char fallback_cmd[64];
            snprintf(fallback_cmd, sizeof(fallback_cmd), "SendGet http://192.168.8.%d/cm?cmnd=Channel3%%20%d", charger_c_ip, dump_load_relay[5]);
            CMD_ExecuteCommand(fallback_cmd, 0);
        }
    } 

    if (!CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE)) 
    {
        if (power < 0.0f) power = 0.0f;
        if (voltage < 0.0f) voltage = 0.0f;
        if (current < 0.0f) current = 0.0f;
    }
    if (CFG_HasFlag(OBK_FLAG_POWER_FORCE_ZERO_IF_RELAYS_OPEN))
    {
        if (Channel_AreAllRelaysOpen()) {
            power = 0;
            current = 0;
        }
    }

    sensors[OBK_VOLTAGE].lastReading = voltage;
    sensors[OBK_CURRENT].lastReading = current;
    sensors[OBK_POWER].lastReading = power;
    sensors[OBK_POWER_APPARENT].lastReading = sensors[OBK_VOLTAGE].lastReading * sensors[OBK_CURRENT].lastReading;
    sensors[OBK_POWER_REACTIVE].lastReading = ((int)net_energy);
    sensors[OBK_POWER_FACTOR].lastReading = (sensors[OBK_POWER_APPARENT].lastReading == 0 ? 1 : sensors[OBK_POWER].lastReading / sensors[OBK_POWER_APPARENT].lastReading);

    lastReadingFrequency = frequency;

    float energy = 0;
    float energy_today_temp = 0;
    if (isnan(energyWh)) {
        xPassedTicks = (int)(xTaskGetTickCount() - energyCounterStamp);
        if (xPassedTicks <= 0)
            xPassedTicks = 1;
        energy = xPassedTicks * power / (3600000.0f / portTICK_PERIOD_MS);
    } 
    else
    {
        if ((int)power>0)
        {
            sensors[OBK_CONSUMPTION_TOTAL].lastReading += energyWh;
            real_consumption += energyWh;
            energy_counter_data += energyWh;
            energy_today_temp = energyWh;
        }
        else
        {
            if (CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE))
            {
                sensors[OBK_GENERATION_TOTAL].lastReading += energyWh;         
                real_export += energyWh;
                energy_counter_data -= energyWh;
            }
        }
    }
              
    energyCounterStamp = xTaskGetTickCount();
    HAL_FlashVars_SaveTotalConsumption(sensors[OBK_CONSUMPTION_TOTAL].lastReading);
    sensors[OBK_CONSUMPTION_TODAY].lastReading  += energy_today_temp;

    if (NTP_IsTimeSynced()) {
        ntpTime = (time_t)NTP_GetCurrentTime();
        ltm = gmtime(&ntpTime);
        if (ConsumptionResetTime == 0)
            ConsumptionResetTime = (time_t)ntpTime;

        if (actual_mday == -1)
        {
            actual_mday = ltm->tm_mday;
        }
        if (actual_mday != ltm->tm_mday)
        {
            for (i = OBK_CONSUMPTION__DAILY_LAST; i >= OBK_CONSUMPTION__DAILY_FIRST; i--) {
                sensors[i].lastReading = sensors[i - 1].lastReading;
            }
            sensors[OBK_CONSUMPTION_TODAY].lastReading = 0.0;
            actual_mday = ltm->tm_mday;

#if WINDOWS
#elif PLATFORM_BL602
#elif PLATFORM_W600 || PLATFORM_W800
#elif PLATFORM_XR809
#elif PLATFORM_BK7231N || PLATFORM_BK7231T
            if (ota_progress()==-1)
#endif
            {
                BL09XX_SaveEmeteringStatistics();
                lastConsumptionSaveStamp = xTaskGetTickCount();
            }
        }
    }

    if (energyCounterStatsEnable == true)
    {
        interval = energyCounterSampleInterval;
        interval *= (1000 / portTICK_PERIOD_MS); 
        if ((xTaskGetTickCount() - energyCounterMinutesStamp) >= interval)
        {
            if (energyCounterMinutes != NULL) {
                sensors[OBK_CONSUMPTION_LAST_HOUR].lastReading = 0;
                for(int i = 0; i < energyCounterSampleCount; i++) {
                    sensors[OBK_CONSUMPTION_LAST_HOUR].lastReading  += energyCounterMinutes[i];
                }
            }
            if ((energyCounterStatsJSONEnable == true) && (MQTT_IsReady() == true))
            {
                root = cJSON_CreateObject();
                cJSON_AddNumberToObject(root, "uptime", g_secondsElapsed);
                cJSON_AddNumberToObject(root, "consumption_total", BL_ChangeEnergyUnitIfNeeded(DRV_GetReading(OBK_CONSUMPTION_TOTAL)));
                cJSON_AddNumberToObject(root, "consumption_last_hour", BL_ChangeEnergyUnitIfNeeded(DRV_GetReading(OBK_CONSUMPTION_LAST_HOUR)));
                cJSON_AddNumberToObject(root, "consumption_stat_index", energyCounterMinutesIndex);
                cJSON_AddNumberToObject(root, "consumption_sample_count", energyCounterSampleCount);
                cJSON_AddNumberToObject(root, "consumption_sampling_period", energyCounterSampleInterval);
                if(NTP_IsTimeSynced() == true)
                {
                    cJSON_AddNumberToObject(root, "consumption_today", BL_ChangeEnergyUnitIfNeeded(DRV_GetReading(OBK_CONSUMPTION_TODAY)));
                    cJSON_AddNumberToObject(root, "consumption_yesterday", BL_ChangeEnergyUnitIfNeeded(DRV_GetReading(OBK_CONSUMPTION_YESTERDAY)));
                    ltm = gmtime(&ConsumptionResetTime);
                    if (NTP_GetTimesZoneOfsSeconds()>0)
                    {
                        snprintf(datetime,sizeof(datetime), "%04i-%02i-%02iT%02i:%02i+%02i:%02i",
                                 ltm->tm_year+1900, ltm->tm_mon+1, ltm->tm_mday, ltm->tm_hour, ltm->tm_min,
                                 NTP_GetTimesZoneOfsSeconds()/3600, (NTP_GetTimesZoneOfsSeconds()/60) % 60);
                    } else {
                        snprintf(datetime, sizeof(datetime), "%04i-%02i-%02iT%02i:%02i-%02i:%02i",
                                 ltm->tm_year+1900, ltm->tm_mon+1, ltm->tm_mday, ltm->tm_hour, ltm->tm_min,
                                 abs(NTP_GetTimesZoneOfsSeconds()/3600), (abs(NTP_GetTimesZoneOfsSeconds())/60) % 60);
                    }
                    cJSON_AddStringToObject(root, "consumption_clear_date", datetime);
                }

                if (energyCounterMinutes != NULL)
                {
                    stats = cJSON_CreateArray();
                    for(i = 0; i < energyCounterSampleCount; i++)
                    {
                        cJSON_AddItemToArray(stats, cJSON_CreateNumber(energyCounterMinutes[i]));
                    }
                    cJSON_AddItemToObject(root, "consumption_samples", stats);
                }

                if(NTP_IsTimeSynced() == true)
                {
                    stats = cJSON_CreateArray();
                    for(i = OBK_CONSUMPTION__DAILY_FIRST; i <= OBK_CONSUMPTION__DAILY_LAST; i++)
                    {
                        cJSON_AddItemToArray(stats, cJSON_CreateNumber(DRV_GetReading(i)));
                    }
                    cJSON_AddItemToObject(root, "consumption_daily", stats);
                }

                msg = cJSON_PrintUnformatted(root);
                cJSON_Delete(root);

                MQTT_PublishMain_StringString("consumption_stats", msg, 0);
                stat_updatesSent++;
                os_free(msg);
            }

            if (energyCounterMinutes != NULL)
            {
                for (i=energyCounterSampleCount-1;i>0;i--)
                {
                    energyCounterMinutes[i] = energyCounterMinutes[i-1];   
                }
                energyCounterMinutes[0] = 0.0;
            }
            energyCounterMinutesStamp = xTaskGetTickCount();
            energyCounterMinutesIndex++;
        }

        if (energyCounterMinutes != NULL)
            energyCounterMinutes[0] += energy_counter_data;
    }

    for(i = OBK__FIRST; i <= OBK__LAST; i++)
    {
        diff = sensors[i].lastSentValue - sensors[i].lastReading;
        if ( ((fabsf(diff) > sensors[i].changeSendThreshold) &&
              (sensors[i].noChangeFrame >= changeDoNotSendMinFrames)) ||
            (sensors[i].noChangeFrame >= changeSendAlwaysFrames) )
        {
            sensors[i].noChangeFrame = 0;

            enum EventCode eventChangeCode;
            switch (i) {
            case OBK_VOLTAGE:                               eventChangeCode = CMD_EVENT_CHANGE_VOLTAGE;                       break;
            case OBK_CURRENT:                               eventChangeCode = CMD_EVENT_CHANGE_CURRENT;                       break;
            case OBK_POWER:                                 eventChangeCode = CMD_EVENT_CHANGE_POWER;                         break;
            case OBK_CONSUMPTION_TOTAL:                     eventChangeCode = CMD_EVENT_CHANGE_CONSUMPTION_TOTAL;             break;
            case OBK_GENERATION_TOTAL:                      eventChangeCode = CMD_EVENT_CHANGE_GENERATION_TOTAL;              break;
            case OBK_CONSUMPTION_LAST_HOUR:                 eventChangeCode = CMD_EVENT_CHANGE_CONSUMPTION_LAST_HOUR;         break;
            default:                                        eventChangeCode = CMD_EVENT_NONE;                                 break;
            }
            switch (eventChangeCode) {
            case CMD_EVENT_NONE:
                break;
            case CMD_EVENT_CHANGE_CURRENT: ;
                int prev_mA = sensors[i].lastSentValue * 1000;
                int now_mA = sensors[i].lastReading * 1000;
                EventHandlers_ProcessVariableChange_Integer(eventChangeCode, prev_mA,now_mA);
                break;
            default:
                EventHandlers_ProcessVariableChange_Integer(eventChangeCode, sensors[i].lastSentValue, sensors[i].lastReading);
                break;
            }

            if (MQTT_IsReady() == true)
            {
                sensors[i].lastSentValue = sensors[i].lastReading;
                if (i == OBK_CONSUMPTION_CLEAR_DATE) {
                    sensors[i].lastReading = ConsumptionResetTime; 
                    ltm = gmtime(&ConsumptionResetTime);
                    if (NTP_GetTimesZoneOfsSeconds()>0)
                    {
                        snprintf(datetime, sizeof(datetime), "%04i-%02i-%02iT%02i:%02i+%02i:%02i",
                                 ltm->tm_year+1900, ltm->tm_mon+1, ltm->tm_mday, ltm->tm_hour, ltm->tm_min,
                                 NTP_GetTimesZoneOfsSeconds()/3600, (NTP_GetTimesZoneOfsSeconds()/60) % 60);
                    } else {
                        snprintf(datetime, sizeof(datetime), "%04i-%02i-%02iT%02i:%02i-%02i:%02i",
                                 ltm->tm_year+1900, ltm->tm_mon+1, ltm->tm_mday, ltm->tm_hour, ltm->tm_min,
                                 abs(NTP_GetTimesZoneOfsSeconds()/3600), (abs(NTP_GetTimesZoneOfsSeconds())/60) % 60);
                    }
                    MQTT_PublishMain_StringString(sensors[i].names.name_mqtt, datetime, 0);
                } else { 
                    float val = sensors[i].lastReading;
                    if (sensors[i].names.units == UNIT_WH) val = BL_ChangeEnergyUnitIfNeeded(val);
                    MQTT_PublishMain_StringFloat(sensors[i].names.name_mqtt, val, sensors[i].rounding_decimals, 0);
                }
                stat_updatesSent++;
            }
        } else {
            sensors[i].noChangeFrame++;
            stat_updatesSkipped++;
        }
    }       

    if (((((sensors[OBK_CONSUMPTION_TOTAL].lastReading - lastSavedEnergyCounterValue) >= changeSavedThresholdEnergy) ||
           ((xTaskGetTickCount() - lastConsumptionSaveStamp) >= (6 * 3600 * 1000 / portTICK_PERIOD_MS)) || 
       ((sensors[OBK_GENERATION_TOTAL].lastReading - lastSavedGenerationCounterValue) >= changeSavedThresholdEnergy)) && (!(CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE))))||(savetoflash == 1))
    {

    savetoflash = 0;
#if WINDOWS
#elif PLATFORM_BL602
#elif PLATFORM_W600 || PLATFORM_W800
#elif PLATFORM_XR809
#elif PLATFORM_BK7231N || PLATFORM_BK7231T
        if (ota_progress() == -1)
#endif
        {
            lastSavedEnergyCounterValue = sensors[OBK_CONSUMPTION_TOTAL].lastReading;
            lastSavedGenerationCounterValue = sensors[OBK_GENERATION_TOTAL].lastReading;
            BL09XX_SaveEmeteringStatistics();
            lastConsumptionSaveStamp = xTaskGetTickCount();
        }
    }
}

void BL_Shared_Init(void)
{
    int i;
    ENERGY_METERING_DATA data;

    for(i = OBK__FIRST; i <= OBK__LAST; i++)
    {
        sensors[i].noChangeFrame = 0;
        sensors[i].lastReading = 0;
    }
    energyCounterStamp = xTaskGetTickCount(); 

    if (energyCounterStatsEnable == true)
    {
        if (energyCounterMinutes == NULL)
        {
            energyCounterMinutes = (float*)os_malloc(energyCounterSampleCount*sizeof(float));
        }
        if (energyCounterMinutes != NULL)
        {
            for(i = 0; i < energyCounterSampleCount; i++)
            {
                energyCounterMinutes[i] = 0.0;
            }   
        }
        energyCounterMinutesStamp = xTaskGetTickCount();
        energyCounterMinutesIndex = 0;
    }

    addLogAdv(LOG_INFO, LOG_FEATURE_ENERGYMETER, "Read ENERGYMETER status values. sizeof(ENERGY_METERING_DATA)=%d\n", sizeof(ENERGY_METERING_DATA));

    HAL_GetEnergyMeterStatus(&data);
    sensors[OBK_CONSUMPTION_TOTAL].lastReading = data.TotalConsumption;
    sensors[OBK_GENERATION_TOTAL].lastReading = data.TotalGeneration;
    sensors[OBK_CONSUMPTION_TODAY].lastReading = data.TodayConsumpion;
    sensors[OBK_CONSUMPTION_YESTERDAY].lastReading = data.YesterdayConsumption;
    actual_mday = data.actual_mday;   
    lastSavedEnergyCounterValue = data.TotalConsumption;
    lastSavedGenerationCounterValue = data.TotalGeneration;
    sensors[OBK_CONSUMPTION_2_DAYS_AGO].lastReading = data.ConsumptionHistory[0];
    sensors[OBK_CONSUMPTION_3_DAYS_AGO].lastReading = data.ConsumptionHistory[1];
    ConsumptionResetTime = data.ConsumptionResetTime;
    ConsumptionSaveCounter = data.save_counter;
    lastConsumptionSaveStamp = xTaskGetTickCount();

    CMD_RegisterCommand("SetDumpLoad", BL09XX_SetDumpLoad, NULL);
    CMD_RegisterCommand("EnergyCntReset", BL09XX_ResetEnergyCounter, NULL);
    CMD_RegisterCommand("ToggleAuto", BL09XX_ToggleAuto, NULL);
    CMD_RegisterCommand("SetupEnergyStats", BL09XX_SetupEnergyStatistic, NULL);
    CMD_RegisterCommand("ConsumptionThreshold", BL09XX_SetupConsumptionThreshold, NULL);
    CMD_RegisterCommand("VCPPublishThreshold", BL09XX_VCPPublishThreshold, NULL);
    CMD_RegisterCommand("VCPPrecision", BL09XX_VCPPrecision, NULL);
    CMD_RegisterCommand("VCPPublishIntervals", BL09XX_VCPPublishIntervals, NULL);
}

float DRV_GetReading(energySensor_t type) 
{
    return sensors[type].lastReading;
}

energySensorNames_t* DRV_GetEnergySensorNames(energySensor_t type)
{
    return &sensors[type].names;
}

// ====================================================================
// NEW JSON API ENDPOINT (Side-by-Side Dual-Bar SVG)
// ====================================================================
int http_fn_api_dash(http_request_t *request) {
    http_setup(request, "application/json");
    poststr(request, "{");

    hprintf255(request, "\"va\":\"%.0fV / %.2fA\",", sensors[OBK_VOLTAGE].lastReading, sensors[OBK_CURRENT].lastReading);
    hprintf255(request, "\"pwr\":\"%.0f W\",", sensors[OBK_POWER].lastReading);
    hprintf255(request, "\"pwr_cls\":\"%s\",", (sensors[OBK_POWER].lastReading < 0) ? "c-exp" : "c-imp");
    hprintf255(request, "\"bal\":\"%.0f Wh\",", sensors[OBK_POWER_REACTIVE].lastReading);
    hprintf255(request, "\"bal_cls\":\"%s\",", (sensors[OBK_POWER_REACTIVE].lastReading < 0) ? "c-exp" : "c-imp");
    hprintf255(request, "\"est\":\"%i Wh\",", estimated_energy_period);
    hprintf255(request, "\"est_cls\":\"%s\",", (estimated_energy_period < 0) ? "c-exp" : "c-imp");

    int dmp = dump_load_relay[5];
    if (dmp == 0) {
        poststr(request, "\"chg_lbl\":\"Charger\",\"chg_v\":\"Idle\",\"chg_c\":\"#888\",");
    } else if (dmp == 5) {
        poststr(request, "\"chg_lbl\":\"Charger\",\"chg_v\":\"Battery\",\"chg_c\":\"#4caf50\",");
    } else {
        hprintf255(request, "\"chg_lbl\":\"Charging\",\"chg_v\":\"%d%%\",\"chg_c\":\"#0099FF\",", dmp);
    }

    hprintf255(request, "\"dmp\":%d,\"auto\":%d,", dmp, charger_c_auto);
    hprintf255(request, "\"clk\":\"%02d:%02d\"", NTP_GetHour(), NTP_GetMinute()); 

    if (CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE) && NTP_IsTimeSynced()) {
        poststr(request, ","); 
        unsigned int minutes_since_midnight = NTP_GetHour() * 60 + NTP_GetMinute();

        poststr(request, "\"sens\":\"");
        for (int i = (OBK__FIRST); i <= (OBK_CONSUMPTION__DAILY_LAST); i++) {
            if (i == OBK_GENERATION_TOTAL && (!CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE))) { i++; }
            if (i <= OBK__NUM_MEASUREMENTS || NTP_IsTimeSynced()) {
                if (i == OBK_VOLTAGE || i == OBK_POWER || i == OBK_CURRENT || i == OBK_POWER_APPARENT || i == OBK_POWER_REACTIVE) continue;
                if ((i == OBK_CONSUMPTION_TOTAL) || (i == OBK_GENERATION_TOTAL)) {
                    hprintf255(request, "<tr><td><b>%s</b></td><td style='text-align:right;'>%.*f kWh</td></tr>",
                               sensors[i].names.name_friendly, sensors[i].rounding_decimals, (0.001*sensors[i].lastReading));
                } else {
                    hprintf255(request, "<tr><td><b>%s</b></td><td style='text-align:right;'>%.*f %s</td></tr>",
                               sensors[i].names.name_friendly, sensors[i].rounding_decimals, sensors[i].lastReading, sensors[i].names.units);
                }
            }
        }
        poststr(request, "\",");

        poststr(request, "\"graph\":\"");
        for (int i = 23; i >= 0; i--) {
            int interval_of_day = (minutes_since_midnight / net_metering_period - i + 96) % 96;
            int c_index = interval_of_day % 32;
            int cons = consumption_matrix[c_index];
            int exp = export_matrix[c_index];
            int net = net_matrix[c_index];
            if (i == 0) { 
                cons += (int)real_consumption;
                exp += (int)real_export;
                net += (int)(real_consumption - real_export); 
            }
            
            int x = (23 - i) * 21 + 2; 
            int h_imp = abs(cons) / 2;
            int h_exp = abs(exp) / 2;
            
            if (h_imp > 120) h_imp = 120;
            if (h_exp > 120) h_exp = 120;
            
            int h_max = (h_imp > h_exp) ? h_imp : h_exp;
            
            if (net != 0 || i == 0) {
                if (net >= 0) {
                    // Both bars point upwards
                    if (h_imp > 0) hprintf255(request, "<rect x='%d' y='%d' width='8' height='%d' fill='#f44336' rx='1'/>", x, 130 - h_imp, h_imp);
                    if (h_exp > 0) hprintf255(request, "<rect x='%d' y='%d' width='8' height='%d' fill='#4caf50' rx='1'/>", x + 9, 130 - h_exp, h_exp);
                } 
                else {
                    // Both bars point downwards
                    if (h_imp > 0) hprintf255(request, "<rect x='%d' y='130' width='8' height='%d' fill='#f44336' rx='1'/>", x, h_imp);
                    if (h_exp > 0) hprintf255(request, "<rect x='%d' y='130' width='8' height='%d' fill='#4caf50' rx='1'/>", x + 9, h_exp);
                }
                
                int text_y = (net >= 0) ? (130 - h_max - 5) : (130 + h_max + 5);
                const char* anchor = (net >= 0) ? "start" : "end";
                hprintf255(request, "<text x='%d' y='%d' fill='#ddd' font-size='14' font-family='sans-serif' text-anchor='%s' transform='rotate(-90 %d %d)' dy='5'>%d</text>",
                           x + 8, text_y, anchor, x + 8, text_y, net);
            } else {
                hprintf255(request, "<text x='%d' y='135' fill='#555' font-size='14' font-family='sans-serif' text-anchor='start' transform='rotate(-90 %d 135)' dy='5'>0</text>", x + 8, x + 8);
            }
        }
        poststr(request, "\"");
    }
    
    poststr(request, "}");
    poststr(request, NULL);
    return 0;
}

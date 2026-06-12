// Internal code ONLY

#include <stdlib.h>   // atof, abs
#include <stdio.h>    // snprintf
#include <string.h>   // memset, strlen

// Charger C mapping constants
#define CHARGER_MIN_PWM   10      // lowest useful duty for the supply
#define CHARGER_MAX_PWM  100

// Set to 48 slots (12-hour circular buffer to match the new 12-hour graph)
#define MATRIX_SIZE 48

static int consumption_matrix[MATRIX_SIZE] = {0}; 
static int export_matrix[MATRIX_SIZE] = {0};
static int net_matrix[MATRIX_SIZE] = {0};

// New Averages matrices
static int charger_c_matrix[MATRIX_SIZE] = {0};
static int inverter_matrix[MATRIX_SIZE] = {0};
static int current_charger_c_accum = 0;
static int current_inverter_accum = 0;
static int sample_count_30s = 0;

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

// NEW GLOBAL TARGETS
static int target_export = 20;
static int target_power = 100;

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

int changeSendAlwaysFrames = 300;
int changeDoNotSendMinFrames = 20;

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
        char fallback_cmd[64];

        dump_load_relay[5] = atoi(args);
        
        snprintf(fallback_cmd, sizeof(fallback_cmd), "SendGet http://192.168.8.%d/cm?cmnd=Channel3%%20%d", charger_c_ip, dump_load_relay[5]);
        CMD_ExecuteCommand(fallback_cmd, 0);
    }
    return CMD_RES_OK;
}

commandResult_t BL09XX_SetTargetPower(const void *context, const char *cmd, const char *args, int cmdFlags)
{
    if(args && *args) {
        int val = atoi(args);
        
        // Ensure values fall into logic limits
        if (val > 5 && val < 18) val = 18;
        if (val > 100) val = 100;
        
        target_power = val;
        
        // Instant execution if manual
        if (charger_c_auto == 0) {
            char fallback_cmd[64];
            dump_load_relay[5] = target_power;

            snprintf(fallback_cmd, sizeof(fallback_cmd), "SendGet http://192.168.8.%d/cm?cmnd=Channel3%%20%d", charger_c_ip, dump_load_relay[5]);
            CMD_ExecuteCommand(fallback_cmd, 0);
        }
    }
    return CMD_RES_OK;
}

commandResult_t BL09XX_SetTargetExport(const void *context, const char *cmd, const char *args, int cmdFlags)
{
    if(args && *args) {
        target_export = atoi(args);
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
    float period_net = 0;
    int process_net_stats = 0;
              
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

        // ======================================================================================================
        // 30-SECOND SAMPLER (Charger & Inverter Averages)
        // ======================================================================================================
        static portTickType last_30s_tick = 0;
        portTickType current_sys_tick = xTaskGetTickCount();
        if ((current_sys_tick - last_30s_tick) >= (30000 / portTICK_PERIOD_MS) || last_30s_tick == 0) {
            last_30s_tick = current_sys_tick;
            int current_dmp = dump_load_relay[5];
            
            if (current_dmp >= 18 && current_dmp <= 100) {
                current_charger_c_accum += current_dmp;
            } else if (current_dmp == 5) {
                current_inverter_accum += 100; // Represent directly as full percentage state
            }
            sample_count_30s++;
        }

        // ------------------------------------------------------------------------------------------------------
        // THE 15-MINUTE RESET & CIRCULAR MATRIX LOGIC 
        // ------------------------------------------------------------------------------------------------------
        {
            int minutes_since_midnight_tracker = (check_hour * 60) + check_time;
            int interval_of_day_tracker = minutes_since_midnight_tracker / 15;
            int current_matrix_index = interval_of_day_tracker % MATRIX_SIZE; 

            if (last_matrix_index == -1) {
                last_matrix_index = current_matrix_index;
            }

            if (current_matrix_index != last_matrix_index) {
                consumption_matrix[last_matrix_index] = (int)real_consumption;
                export_matrix[last_matrix_index] = (int)real_export;
                net_matrix[last_matrix_index] = (int)real_consumption - (int)real_export;

                // Write averages for the interval
                charger_c_matrix[last_matrix_index] = sample_count_30s ? (current_charger_c_accum / sample_count_30s) : 0;
                inverter_matrix[last_matrix_index] = sample_count_30s ? (current_inverter_accum / sample_count_30s) : 0;

                // Process Net Metering for the interval
                period_net = real_consumption - real_export;
                process_net_stats = 1;

                real_export = 0;
                real_consumption = 0;
                net_energy = 0;
                energyCounterMinutesIndex = 0;
                lastsync = 0; 
                
                consumption_matrix[current_matrix_index] = 0;
                export_matrix[current_matrix_index] = 0;
                net_matrix[current_matrix_index] = 0;
                charger_c_matrix[current_matrix_index] = 0;
                inverter_matrix[current_matrix_index] = 0;

                current_charger_c_accum = 0;
                current_inverter_accum = 0;
                sample_count_30s = 0;

                last_matrix_index = current_matrix_index;
                savetoflash = 1;
            }
        }

        if (!(check_time == old_time))
        {
            min_reset = 1;
            old_time = check_time;
            lastsync++;
        }
                                                         
        net_energy = (real_consumption - real_export);                               

        // ======================================================================================================
        // CONTROL LOGIC (Target Export, Proportional-Integral Control)
        // ======================================================================================================
        static portTickType last_control_tick = 0;
        portTickType current_tick = xTaskGetTickCount();
        
        if ((current_tick - last_control_tick) >= (30000 / portTICK_PERIOD_MS) || last_control_tick == 0) 
        {
            int min_in_block;
            int check_time_estimate_mins;
            char fallback_cmd[64];

            last_control_tick = current_tick;
            
            min_in_block = check_time % 15; 
            check_time_estimate_mins = 15 - min_in_block; 
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
            if (net_energy < -((float)target_export + 10.0f)) {
                solar_available = 1;
            } else if (net_energy > 10.0f) {
                solar_available = 0;
            }

            // ====================================================================
            // ISOLATED LOGIC BLOCK (AUTO / MANUAL)
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
                    solar_excess = 0; 
                } 
                else {
                    if (net_energy > -((float)target_export)) {
                        solar_excess = 0; 
                    } else {
                        int excess_wh, error_w, pwm_step;

                        excess_wh = -(estimated_energy_period + target_export); 
                        
                        // Convert Wh error into Watts over the remaining time
                        error_w = (excess_wh * 60) / check_time_estimate_mins; 
                        
                        // Convert Watts to PWM step (10W = 1 PWM unit) dampened by half
                        pwm_step = (error_w / 10) / 2; 
                        
                        solar_excess += pwm_step;
                    }
                    
                    // Enforce absolute constraints
                    if (solar_excess > 82) solar_excess = 82;
                    if (solar_excess < 0) solar_excess = 0;
                    
                    persistent_state = 18 + solar_excess;
                    
                    int active_max = target_power;
                    if (active_max < 18) active_max = 100;
                    
                    if (persistent_state > active_max) persistent_state = active_max;
                }
                
                dump_load_relay[5] = persistent_state;

                // Send Commands via process loop
                snprintf(fallback_cmd, sizeof(fallback_cmd), "SendGet http://192.168.8.%d/cm?cmnd=Channel3%%20%d", charger_c_ip, dump_load_relay[5]);
                CMD_ExecuteCommand(fallback_cmd, 0);
            } // END OF AUTO BLOCK
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
            real_consumption += energyWh;
        }
        else
        {
            if (CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE))
            {
                real_export += energyWh;
            }
        }
    }
              
    if (process_net_stats == 1) {
        if (period_net > 0) {
            sensors[OBK_CONSUMPTION_TOTAL].lastReading += period_net;
            sensors[OBK_CONSUMPTION_TODAY].lastReading += period_net;
            energy_counter_data = period_net;
        } else if (period_net < 0) {
            sensors[OBK_GENERATION_TOTAL].lastReading += (-period_net);
            energy_counter_data = period_net;
        }
    }

    energyCounterStamp = xTaskGetTickCount();
    HAL_FlashVars_SaveTotalConsumption(sensors[OBK_CONSUMPTION_TOTAL].lastReading);

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
                for(int j = 0; j < energyCounterSampleCount; j++) {
                    sensors[OBK_CONSUMPTION_LAST_HOUR].lastReading  += energyCounterMinutes[j];
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
                    for(int k = 0; k < energyCounterSampleCount; k++)
                    {
                        cJSON_AddItemToArray(stats, cJSON_CreateNumber(energyCounterMinutes[k]));
                    }
                    cJSON_AddItemToObject(root, "consumption_samples", stats);
                }

                if(NTP_IsTimeSynced() == true)
                {
                    stats = cJSON_CreateArray();
                    for(int m = OBK_CONSUMPTION__DAILY_FIRST; m <= OBK_CONSUMPTION__DAILY_LAST; m++)
                    {
                        cJSON_AddItemToArray(stats, cJSON_CreateNumber(DRV_GetReading(m)));
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
                for (int n=energyCounterSampleCount-1; n>0; n--)
                {
                    energyCounterMinutes[n] = energyCounterMinutes[n-1];   
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
            enum EventCode eventChangeCode;
            sensors[i].noChangeFrame = 0;

            switch (i) {
            case OBK_VOLTAGE:                                   eventChangeCode = CMD_EVENT_CHANGE_VOLTAGE;                       break;
            case OBK_CURRENT:                                   eventChangeCode = CMD_EVENT_CHANGE_CURRENT;                       break;
            case OBK_POWER:                                     eventChangeCode = CMD_EVENT_CHANGE_POWER;                         break;
            case OBK_CONSUMPTION_TOTAL:                         eventChangeCode = CMD_EVENT_CHANGE_CONSUMPTION_TOTAL;             break;
            case OBK_GENERATION_TOTAL:                          eventChangeCode = CMD_EVENT_CHANGE_GENERATION_TOTAL;              break;
            case OBK_CONSUMPTION_LAST_HOUR:                     eventChangeCode = CMD_EVENT_CHANGE_CONSUMPTION_LAST_HOUR;         break;
            default:                                            eventChangeCode = CMD_EVENT_NONE;                                 break;
            }
            switch (eventChangeCode) {
            case CMD_EVENT_NONE:
                break;
            case CMD_EVENT_CHANGE_CURRENT: 
            {
                int prev_mA = sensors[i].lastSentValue * 1000;
                int now_mA = sensors[i].lastReading * 1000;
                EventHandlers_ProcessVariableChange_Integer(eventChangeCode, prev_mA,now_mA);
                break;
            }
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
    CMD_RegisterCommand("SetTargetPower", BL09XX_SetTargetPower, NULL);
    CMD_RegisterCommand("SetTargetExport", BL09XX_SetTargetExport, NULL);
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
// NEW JSON API ENDPOINT (Smooth Area Chart Generation)
// EXACTLY as provided in the attached stable file
// ====================================================================
int http_fn_api_dash(http_request_t *request) {
    int dmp;
    http_setup(request, "application/json");
    poststr(request, "{");

    hprintf255(request, "\"va\":\"%.0fV / %.2fA\",", sensors[OBK_VOLTAGE].lastReading, sensors[OBK_CURRENT].lastReading);
    hprintf255(request, "\"pwr\":\"%.0f W\",", sensors[OBK_POWER].lastReading);
    hprintf255(request, "\"pwr_cls\":\"%s\",", (sensors[OBK_POWER].lastReading < 0) ? "c-exp" : "c-imp");
    hprintf255(request, "\"bal\":\"%.0f Wh\",", sensors[OBK_POWER_REACTIVE].lastReading);
    hprintf255(request, "\"bal_cls\":\"%s\",", (sensors[OBK_POWER_REACTIVE].lastReading < 0) ? "c-exp" : "c-imp");
    hprintf255(request, "\"est\":\"%i Wh\",", estimated_energy_period);
    hprintf255(request, "\"est_cls\":\"%s\",", (estimated_energy_period < 0) ? "c-exp" : "c-imp");

    dmp = dump_load_relay[5];
    if (dmp == 0) {
        poststr(request, "\"chg_lbl\":\"Charger\",\"chg_v\":\"Idle\",\"chg_c\":\"#888\",");
    } else if (dmp == 5) {
        poststr(request, "\"chg_lbl\":\"Charger\",\"chg_v\":\"Battery\",\"chg_c\":\"#4caf50\",");
    } else {
        hprintf255(request, "\"chg_lbl\":\"Charging\",\"chg_v\":\"%d%%\",\"chg_c\":\"#0099FF\",", dmp);
    }

    hprintf255(request, "\"dmp\":%d,\"auto\":%d,", dmp, charger_c_auto);
    hprintf255(request, "\"t_pwr\":%d,\"t_exp\":%d,", target_power, target_export);
    hprintf255(request, "\"clk\":\"%02d:%02d\"", NTP_GetHour(), NTP_GetMinute()); 

    if (CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE) && NTP_IsTimeSynced()) {
        unsigned int minutes_since_midnight = NTP_GetHour() * 60 + NTP_GetMinute();
        int p_i;

        poststr(request, ","); 
        poststr(request, "\"sens\":\"");
        
        for (p_i = (OBK__FIRST); p_i <= (OBK_CONSUMPTION__DAILY_LAST); p_i++) {
            if (p_i == OBK_GENERATION_TOTAL && (!CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE))) { p_i++; }
            if (p_i <= OBK__NUM_MEASUREMENTS || NTP_IsTimeSynced()) {
                if (p_i == OBK_VOLTAGE || p_i == OBK_POWER || p_i == OBK_CURRENT || p_i == OBK_POWER_APPARENT || p_i == OBK_POWER_REACTIVE) continue;
                if ((p_i == OBK_CONSUMPTION_TOTAL) || (p_i == OBK_GENERATION_TOTAL)) {
                    hprintf255(request, "<tr><td><b>%s</b></td><td style='text-align:right;'>%.*f kWh</td></tr>",
                               sensors[p_i].names.name_friendly, sensors[p_i].rounding_decimals, (0.001*sensors[p_i].lastReading));
                } else {
                    hprintf255(request, "<tr><td><b>%s</b></td><td style='text-align:right;'>%.*f %s</td></tr>",
                               sensors[p_i].names.name_friendly, sensors[p_i].rounding_decimals, sensors[p_i].lastReading, sensors[p_i].names.units);
                }
            }
        }
        poststr(request, "\",");

        poststr(request, "\"graph\":\"");
        
        // 1. Draw the filled area (polygon) mapped to the red/green gradient (Lower Main Graph)
        poststr(request, "<polygon fill='url(#splitFade)' points='60,225 ");
        for (int i = 47; i >= 0; i--) {
            int interval_of_day, c_index, net, x, h, y;
            char point_str[32];
            
            interval_of_day = (minutes_since_midnight / net_metering_period - i + 96) % 96;
            c_index = interval_of_day % MATRIX_SIZE;
            net = net_matrix[c_index];
            if (i == 0) { net += (int)(real_consumption - real_export); }
            
            x = (47 - i) * 11 + 60; 
            h = net / 2;
            if (h > 150) h = 150;
            if (h < -75) h = -75;
            y = 225 - h;
            
            snprintf(point_str, sizeof(point_str), "%d,%d ", x, y);
            poststr(request, point_str);
        }
        poststr(request, "577,225'/>");

        // 2. Draw the crisp defining line on top of the fill
        poststr(request, "<polyline fill='none' stroke='#888' stroke-width='2' points='");
        for (int i = 47; i >= 0; i--) {
            int interval_of_day, c_index, net, x, h, y;
            char point_str[32];
            
            interval_of_day = (minutes_since_midnight / net_metering_period - i + 96) % 96;
            c_index = interval_of_day % MATRIX_SIZE;
            net = net_matrix[c_index];
            if (i == 0) { net += (int)(real_consumption - real_export); }
            
            x = (47 - i) * 11 + 60; 
            h = net / 2;
            if (h > 150) h = 150;
            if (h < -75) h = -75;
            y = 225 - h;
            
            snprintf(point_str, sizeof(point_str), "%d,%d ", x, y);
            poststr(request, point_str);
        }
        poststr(request, "'/>");

        // 3. Draw the Charger Overlay (Top isolated graph box, Y:10 to Y:60)
        poststr(request, "<polyline fill='none' stroke='#4caf50' stroke-width='1' points='");
        for (int i = 47; i >= 0; i--) {
            int interval_of_day = (minutes_since_midnight / net_metering_period - i + 96) % 96;
            int c_index = interval_of_day % MATRIX_SIZE;
            int val = charger_c_matrix[c_index];
            if (i == 0 && sample_count_30s > 0) { val = current_charger_c_accum / sample_count_30s; }
            int x = (47 - i) * 11 + 60;
            int y = 60 - (val / 2); 
            hprintf255(request, "%d,%d ", x, y);
        }
        poststr(request, "'/>");

        // 4. Draw the Inverter Overlay (Top isolated graph box, Y:10 to Y:60)
        poststr(request, "<polyline fill='none' stroke='#ff9800' stroke-width='1' points='");
        for (int i = 47; i >= 0; i--) {
            int interval_of_day = (minutes_since_midnight / net_metering_period - i + 96) % 96;
            int c_index = interval_of_day % MATRIX_SIZE;
            int val = inverter_matrix[c_index];
            if (i == 0 && sample_count_30s > 0) { val = current_inverter_accum / sample_count_30s; }
            int x = (47 - i) * 11 + 60;
            int y = 60 - (val / 2); 
            hprintf255(request, "%d,%d ", x, y);
        }
        poststr(request, "'/>\"");
    }
    
    poststr(request, "}");
    poststr(request, NULL);
    return 0;
}

// ====================================================================
// NEW STANDALONE DASHBOARD (Legacy Browser Compatible & Chunked)
// ====================================================================
int http_fn_custom_dash(http_request_t *request) {
    http_setup(request, "text/html");

    poststr(request, "<!DOCTYPE html><html><head><meta charset='utf-8'><meta name='viewport' content='width=device-width, initial-scale=1.0'>");
    poststr(request, "<title>Solar Dashboard</title><style>");
    poststr(request, "body { margin: 0; background-color: #000; display: -webkit-box; display: -webkit-flex; display: flex; -webkit-box-pack: center; -webkit-justify-content: center; justify-content: center; }");
    poststr(request, "#dash-container { max-width: 1200px; width: 100%; min-height: 100vh; background-color: #121212; padding: 10px 20px 20px 20px; box-sizing: border-box; font-family: -apple-system, sans-serif; color: #eee; position: relative; }");
    poststr(request, ".top-stats { display: -webkit-box; display: -webkit-flex; display: flex; -webkit-box-pack: justify; -webkit-justify-content: space-between; justify-content: space-between; -webkit-box-align: center; -webkit-align-items: center; align-items: center; background: #222; padding: 18px; border-radius: 8px; text-align: center; margin-top: 15px; width: 100%; box-sizing: border-box; -webkit-flex-wrap: nowrap; flex-wrap: nowrap; white-space: nowrap; }");
    poststr(request, ".top-stats div { display: -webkit-box; display: -webkit-flex; display: flex; -webkit-box-orient: vertical; -webkit-box-direction: normal; -webkit-flex-direction: column; flex-direction: column; -webkit-box-pack: center; -webkit-justify-content: center; justify-content: center; margin: 0 10px; }");
    poststr(request, ".top-stats label { color: #888; font-size: 20px; text-transform: uppercase; margin-bottom: 6px; display: block; } .top-stats b { font-size: 38px; font-weight: 600; } .c-exp { color: #4caf50; } .c-imp { color: #f44336; }");
    poststr(request, ".dash-row { display: -webkit-box; display: -webkit-flex; display: flex; -webkit-box-orient: horizontal; -webkit-box-direction: normal; -webkit-flex-direction: row; flex-direction: row; margin-top: 15px; height: 400px; -webkit-box-align: stretch; -webkit-align-items: stretch; align-items: stretch; }");
    poststr(request, ".left-col { -webkit-box-flex: 0; -webkit-flex: 0 0 230px; flex: 0 0 230px; width: 230px; background: #222; padding: 10px; border-radius: 8px; overflow-y: auto; margin-right: 15px; box-sizing: border-box; }");
    poststr(request, ".sens-tbl { width: 100%; font-size: 14px; border-collapse: collapse; } .sens-tbl td { padding: 5px 0; border-bottom: 1px solid #333; }");
    poststr(request, ".graph-col { -webkit-box-flex: 1; -webkit-flex: 1; flex: 1; background: #222; padding: 15px; border-radius: 8px; display: -webkit-box; display: -webkit-flex; display: flex; -webkit-box-orient: vertical; -webkit-box-direction: normal; -webkit-flex-direction: column; flex-direction: column; -webkit-box-align: center; -webkit-align-items: center; align-items: center; -webkit-box-pack: center; -webkit-justify-content: center; justify-content: center; overflow: hidden; position: relative; box-sizing: border-box; margin-right: 15px; }");
    poststr(request, ".right-col { -webkit-box-flex: 0; -webkit-flex: 0 0 280px; flex: 0 0 280px; width: 280px; background: #222; padding: 20px; border-radius: 8px; display: -webkit-box; display: -webkit-flex; display: flex; -webkit-box-orient: vertical; -webkit-box-direction: normal; -webkit-flex-direction: column; flex-direction: column; box-sizing: border-box; }");
    poststr(request, ".btn-tgl { width: 100%; height: 50px; border: none; color: white; border-radius: 6px; font-weight: bold; cursor: pointer; font-size: 16px; margin-bottom: 12px; display: block; }");
    poststr(request, ".sld-v-block { margin-top: 10px; width: 100%; } .sld-v-block label { display: block; font-size: 11px; color: #888; margin-bottom: 6px; text-transform: uppercase; letter-spacing: 0.5px; }");
    poststr(request, ".bottom-clk-row { background: #222; border-radius: 8px; padding: 25px; margin-top: 15px; display: -webkit-box; display: -webkit-flex; display: flex; -webkit-box-orient: horizontal; -webkit-box-direction: normal; -webkit-flex-direction: row; flex-direction: row; -webkit-box-align: center; -webkit-align-items: center; align-items: center; -webkit-box-pack: center; -webkit-justify-content: center; justify-content: center; box-sizing: border-box; width: 100%; }");
    poststr(request, ".clk-text-wrap { display: -webkit-box; display: -webkit-flex; display: flex; -webkit-box-orient: vertical; -webkit-box-direction: normal; -webkit-flex-direction: column; flex-direction: column; -webkit-box-align: start; -webkit-align-items: flex-start; align-items: flex-start; margin-left: 20px; text-align: left; }");
    poststr(request, "#d-clk { font-size: 120px; font-weight: bold; color: #0099FF; font-family: monospace; line-height: 1; letter-spacing: -3px; }");
    poststr(request, "#d-day { font-size: 26px; font-weight: 600; color: #eee; text-transform: uppercase; font-family: sans-serif; letter-spacing: 2px; margin-bottom: 4px; } #d-date { font-size: 16px; color: #888; font-family: sans-serif; }");
    poststr(request, ".close-btn { position: absolute; top: 10px; right: 15px; font-size: 16px; color: #666; cursor: pointer; z-index: 10; }");
    poststr(request, "</style></head><body>");

    poststr(request, "<div id='dash-container'><div class='close-btn' onclick='window.location.href=\"/index\"'>✕</div>");
    poststr(request, "<div class='top-stats'><div><label>Voltage & Current</label><b id='d-va'>--</b></div>");
    poststr(request, "<div><label>Power</label><b id='d-pwr'>--</b></div><div><label>Now / 15min Est.</label><b><span id='d-bal'>--</span> / <span id='d-est'>--</span></b></div>");
    poststr(request, "<div id='d-chg-box'><label id='c-lbl'>Charger</label><b id='c-v'>--</b></div></div>");
    
    if (CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE)) {
        poststr(request, "<div class='dash-row'><div class='left-col'><div style='font-size:12px; color:#888; margin-bottom:8px; text-transform:uppercase;'>Sensor Data</div>");
        poststr(request, "<table class='sens-tbl'><tbody id='d-sens-body'></tbody></table>");
        poststr(request, "<div style='margin-top:20px; font-size:11px; color:#aaa; padding:12px; background:#1a1a1a; border-radius:6px; border:1px solid #333;'>");
        poststr(request, "<div style='margin-bottom:8px; color:#888; text-transform:uppercase; font-size:10px; letter-spacing:1px;'>Graph Legend</div>");
        poststr(request, "<div><span style='display:inline-block; width:14px; height:2px; background:#888; margin-right:8px; vertical-align:middle;'></span>Total Energy</div>");
        poststr(request, "<div style='margin-top:8px;'><span style='display:inline-block; width:14px; height:2px; background:#4caf50; margin-right:8px; vertical-align:middle;'></span>Charger Average</div>");
        poststr(request, "<div style='margin-top:8px;'><span style='display:inline-block; width:14px; height:2px; background:#ff9800; margin-right:8px; vertical-align:middle;'></span>Inverter Average</div></div></div>");

        poststr(request, "<div class='graph-col'><svg viewBox='0 0 592 340' preserveAspectRatio='xMinYMid meet' style='width:100%; height:100%; background:transparent;'>");
        poststr(request, "<defs><linearGradient id='splitFade' x1='0' y1='0' x2='0' y2='340' gradientUnits='userSpaceOnUse'>");
        poststr(request, "<stop offset='75' stop-color='#f44336' stop-opacity='0.6'/><stop offset='225' stop-color='#f44336' stop-opacity='0'/>");
        poststr(request, "<stop offset='225' stop-color='#4caf50' stop-opacity='0'/><stop offset='300' stop-color='#4caf50' stop-opacity='0.6'/>");
        poststr(request, "</linearGradient></defs><rect x='60' y='10' width='517' height='50' fill='#181818'/>");
        poststr(request, "<rect x='60' y='75' width='517' height='235' fill='#181818'/><line x1='60' y1='10' x2='60' y2='60' stroke='#777' stroke-width='1'/>");
        poststr(request, "<line x1='60' y1='75' x2='60' y2='310' stroke='#777' stroke-width='1'/><line x1='60' y1='60' x2='577' y2='60' stroke='#777' stroke-width='1'/>");
        poststr(request, "<g stroke='#333' stroke-width='1' stroke-dasharray='5,5'><line x1='60' y1='35' x2='577' y2='35'/><line x1='60' y1='75' x2='577' y2='75'/>");
        poststr(request, "<line x1='60' y1='150' x2='577' y2='150'/><line x1='60' y1='300' x2='577' y2='300'/></g>");
        poststr(request, "<line x1='60' y1='225' x2='577' y2='225' stroke='#777' stroke-width='1.5'/>");
        poststr(request, "<g fill='#888' font-size='12' font-family='monospace' text-anchor='end'><text x='48' y='14'>100</text><text x='48' y='64'>0</text>");
        poststr(request, "<text x='48' y='79'>+300</text><text x='48' y='154'>+150</text><text x='48' y='229' fill='#aaa'>0 Wh</text><text x='48' y='304'>-150</text></g>");
        poststr(request, "<g id='d-graph-data'></g>");

        poststr(request, "<g stroke='#777' stroke-width='1'><line x1='60' y1='310' x2='577' y2='310'/></g>");
        poststr(request, "<g fill='#888' font-size='10' font-family='sans-serif'>");
        for (int i = 0; i <= 47; i++) {
            int x = (47 - i) * 11 + 60;
            if (i % 4 == 0) {
                hprintf255(request, "<line x1='%d' y1='310' x2='%d' y2='316' stroke='#777'/>", x, x);
                if (i == 0) {
                    hprintf255(request, "<text x='%d' y='328' text-anchor='end'>Now</text>", x);
                } else {
                    hprintf255(request, "<text x='%d' y='328' text-anchor='middle'>-%dh</text>", x, i/4);
                }
            } else {
                hprintf255(request, "<line x1='%d' y1='310' x2='%d' y2='313' stroke='#777'/>", x, x);
            }
        }
        poststr(request, "</g>");

        poststr(request, "</svg></div><div class='right-col'>");
        poststr(request, "<div style='font-size:12px; color:#888; text-transform:uppercase; margin-bottom:12px;'>System Modes</div>");
        poststr(request, "<button id='m-btn' class='btn-tgl' onclick='tm()'>--</button><button id='inv-btn' class='btn-tgl' onclick='t_inv()'>INVERTER</button>");
        poststr(request, "<button id='chg-btn' class='btn-tgl' onclick='t_chg()'>CHARGER</button>");
        poststr(request, "<div style='font-size:12px; color:#888; text-transform:uppercase; margin-top:10px; margin-bottom:5px;'>Parameters</div>");
        poststr(request, "<div class='sld-v-block'><label>Max Power / Manual (<span id='lbl-pwr'></span>%)</label>");
        poststr(request, "<input type='range' id='sld-pwr' min='18' max='100' value='100' onchange='s_pwr(this.value)' style='width:100%;'></div>");
        poststr(request, "<div class='sld-v-block' style='margin-top:15px;'><label>Target Export (<span id='lbl-exp'></span> Wh)</label>");
        poststr(request, "<input type='range' id='sld-exp' min='10' max='100' value='20' onchange='s_exp(this.value)' style='width:100%;'></div></div></div>");
        
        poststr(request, "<div class='bottom-clk-row'><div id='d-clk'>--:--</div><div class='clk-text-wrap'>");
        poststr(request, "<div id='d-day'>--</div><div id='d-date'>--</div></div></div>");
    }
    
    poststr(request, "</div><script>");
    poststr(request, "var dmp=0, auto=0;");
    poststr(request, "function s_pwr(v){ var xhr=new XMLHttpRequest(); xhr.open('GET','/cm?cmnd=SetTargetPower%20'+v,true); xhr.send(); document.getElementById('lbl-pwr').innerText=v; }");
    poststr(request, "function s_exp(v){ var xhr=new XMLHttpRequest(); xhr.open('GET','/cm?cmnd=SetTargetExport%20'+v,true); xhr.send(); document.getElementById('lbl-exp').innerText=v; }");
    poststr(request, "function upd(v){if(auto===1)return; if(v>=18){document.getElementById('sld-pwr').value=v;} s_pwr(v); dmp=parseInt(v, 10); btnColor();}");
    poststr(request, "function t_inv(){upd(dmp===5?0:5);} function t_chg(){upd(dmp>=10?0:18);}");
    poststr(request, "function tm(){auto=(auto===1)?0:1; var xhr=new XMLHttpRequest(); xhr.open('GET','/cm?cmnd=ToggleAuto',true); xhr.send(); btnColor();}");
    poststr(request, "function btnColor(){ var i=document.getElementById('inv-btn'),c=document.getElementById('chg-btn'),m=document.getElementById('m-btn');");
    poststr(request, "if(i) i.style.background=(dmp===5)?'#ff9800':'#555'; if(c) c.style.background=(dmp>18)?'#4caf50':((dmp>=10&&dmp<=18)?'#8bc34a':'#555');");
    poststr(request, "if(m){ m.innerText=(auto===1)?'AUTO':'MANUAL'; m.style.background=(auto===1)?'#0099FF':'#f44336'; } }");
    poststr(request, "function refresh(){ var xhr=new XMLHttpRequest(); xhr.onreadystatechange=function(){");
    poststr(request, "if(xhr.readyState===4 && xhr.status===200){ try { var d=JSON.parse(xhr.responseText);");
    poststr(request, "document.getElementById('d-va').innerText=d.va; document.getElementById('d-pwr').innerText=d.pwr; document.getElementById('d-pwr').className=d.pwr_cls;");
    poststr(request, "document.getElementById('d-bal').innerText=d.bal; document.getElementById('d-bal').className=d.bal_cls; document.getElementById('d-est').innerText=d.est;");
    poststr(request, "document.getElementById('d-est').className=d.est_cls; document.getElementById('c-lbl').innerText=d.chg_lbl; document.getElementById('c-v').innerText=d.chg_v;");
    poststr(request, "document.getElementById('c-v').style.color=d.chg_c; document.getElementById('d-clk').innerText=d.clk;");
    poststr(request, "if(d.t_pwr>=18){document.getElementById('sld-pwr').value=d.t_pwr;} document.getElementById('lbl-pwr').innerText=d.t_pwr;");
    poststr(request, "document.getElementById('sld-exp').value=d.t_exp; document.getElementById('lbl-exp').innerText=d.t_exp;");
    poststr(request, "dmp=d.dmp; auto=d.auto; btnColor(); if(d.sens){ document.getElementById('d-sens-body').innerHTML=d.sens; document.getElementById('d-graph-data').innerHTML=d.graph; }");
    poststr(request, "var days=['SUNDAY','MONDAY','TUESDAY','WEDNESDAY','THURSDAY','FRIDAY','SATURDAY']; var dt=new Date();");
    poststr(request, "document.getElementById('d-day').innerText=days[dt.getDay()];");
    poststr(request, "document.getElementById('d-date').innerText=dt.toLocaleDateString(undefined,{year:'numeric',month:'long',day:'numeric'});");
    poststr(request, "} catch(e) {} } }; xhr.open('GET','/api_dash?t='+Date.now(),true); xhr.send(); }");
    poststr(request, "refresh(); setInterval(refresh, 10000); </script></body></html>");
    
    poststr(request, NULL);
    return 0;
}

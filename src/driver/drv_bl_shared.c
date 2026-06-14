// Internal code ONLY

#include <stdlib.h>   // atof, abs
#include <stdio.h>    // snprintf
#include <string.h>   // memset, strlen

// Charger C mapping constants
#define CHARGER_MIN_PWM   10       // lowest useful duty for the supply
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

// ====================================================================
// ENERGY VERSION COUNTER (global)
// ====================================================================
int energy_version = 0;
void mark_energy_dirty(void) { energy_version++; }

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
    mark_energy_dirty();
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
        mark_energy_dirty();
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
            mark_energy_dirty();

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
            mark_energy_dirty();
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
// JSON API ENDPOINT
// ====================================================================
int http_fn_api_dash(http_request_t *request) {
    const char *req_param = NULL;
    if (request->url) req_param = strstr(request->url, "req=");

    http_setup(request, "application/json");

    char buf[512];
    int  pos     = 0;
    int  has_ntp = CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE) && NTP_IsTimeSynced();

#define B(...) pos += snprintf(buf + pos, sizeof(buf) - pos, __VA_ARGS__)

    B("{");

    // ---- CORE (default or req=core) ----
    if (!req_param || strncmp(req_param, "req=core", 8) == 0) {
        int dmp = dump_load_relay[5];

        B("\"va\":\"%.0fV / %.2fA\","
          "\"pwr\":\"%.0f W\","
          "\"pwr_cls\":\"%s\","
          "\"bal\":\"%.0f Wh\","
          "\"bal_cls\":\"%s\","
          "\"est\":\"%i Wh\","
          "\"est_cls\":\"%s\",",
          sensors[OBK_VOLTAGE].lastReading, sensors[OBK_CURRENT].lastReading,
          sensors[OBK_POWER].lastReading,
          sensors[OBK_POWER].lastReading          < 0 ? "c-exp" : "c-imp",
          sensors[OBK_POWER_REACTIVE].lastReading,
          sensors[OBK_POWER_REACTIVE].lastReading  < 0 ? "c-exp" : "c-imp",
          estimated_energy_period,
          estimated_energy_period                  < 0 ? "c-exp" : "c-imp");

        if      (dmp == 0) B("\"chg_v\":\"Idle\",\"chg_c\":\"#888\",");
        else if (dmp == 5) B("\"chg_v\":\"Battery\",\"chg_c\":\"#4caf50\",");
        else               B("\"chg_v\":\"%d%%\",\"chg_c\":\"#0099FF\",", dmp);

        B("\"dmp\":%d,\"auto\":%d,"
          "\"t_pwr\":%d,\"t_exp\":%d,"
          "\"clk\":\"%02d:%02d\"",
          dmp, charger_c_auto,
          target_power, target_export,
          NTP_GetHour(), NTP_GetMinute());

        if (has_ntp) B(",\"ev\":%d", energy_version);
    }

    // ---- ENERGY TOTALS (req=energy) ----
    else if (strncmp(req_param, "req=energy", 10) == 0 && has_ntp) {
        B("\"pf\":\"%.*f\","
          "\"econs\":\"%.*f kWh\","
          "\"egen\":\"%.*f kWh\","
          "\"clh\":\"%.*f Wh\","
          "\"ctoday\":\"%.*f Wh\","
          "\"cyest\":\"%.*f Wh\","
          "\"c2d\":\"%.*f Wh\","
          "\"c3d\":\"%.*f Wh\","
          "\"ev\":%d",
          sensors[OBK_POWER_FACTOR].rounding_decimals,
              sensors[OBK_POWER_FACTOR].lastReading,
          sensors[OBK_CONSUMPTION_TOTAL].rounding_decimals,
              0.001 * sensors[OBK_CONSUMPTION_TOTAL].lastReading,
          sensors[OBK_GENERATION_TOTAL].rounding_decimals,
              0.001 * sensors[OBK_GENERATION_TOTAL].lastReading,
          sensors[OBK_CONSUMPTION_LAST_HOUR].rounding_decimals,
              sensors[OBK_CONSUMPTION_LAST_HOUR].lastReading,
          sensors[OBK_CONSUMPTION_TODAY].rounding_decimals,
              sensors[OBK_CONSUMPTION_TODAY].lastReading,
          sensors[OBK_CONSUMPTION_YESTERDAY].rounding_decimals,
              sensors[OBK_CONSUMPTION_YESTERDAY].lastReading,
          sensors[OBK_CONSUMPTION_2_DAYS_AGO].rounding_decimals,
              sensors[OBK_CONSUMPTION_2_DAYS_AGO].lastReading,
          sensors[OBK_CONSUMPTION_3_DAYS_AGO].rounding_decimals,
              sensors[OBK_CONSUMPTION_3_DAYS_AGO].lastReading,
          energy_version);
    }

    // ---- GRAPH ARRAYS (req=net | req=chg | req=inv) ----
    else if (has_ntp && req_param) {
        unsigned int msm      = NTP_GetHour() * 60 + NTP_GetMinute();
        const char  *key      = NULL;
        int         *matrix   = NULL;
        int          is_additive = 0, has_live = 0, live_val = 0;

        if (strncmp(req_param, "req=net", 7) == 0) {
            key    = "net"; matrix = net_matrix;
            live_val    = (int)(real_consumption - real_export);
            has_live    = 1; is_additive = 1;
        } else if (strncmp(req_param, "req=chg", 7) == 0) {
            key    = "chg"; matrix = charger_c_matrix;
            has_live    = (sample_count_30s > 0);
            if (has_live) live_val = current_charger_c_accum / sample_count_30s;
        } else if (strncmp(req_param, "req=inv", 7) == 0) {
            key    = "inv"; matrix = inverter_matrix;
            has_live    = (sample_count_30s > 0);
            if (has_live) live_val = current_inverter_accum / sample_count_30s;
        }

        if (key && matrix) {
            B("\"%s\":[", key);
            for (int i = 47; i >= 0; i--) {
                int idx = (msm / net_metering_period - i + 96) % 96;
                int val = matrix[idx % MATRIX_SIZE];
                if (i == 0 && has_live)
                    val = is_additive ? val + live_val : live_val;
                B("%d%s", val, i == 0 ? "" : ",");
            }
            B("]");
        }
    }

    B("}");
    buf[pos] = '\0';
    poststr(request, buf);
    poststr(request, NULL);

#undef B
    return 0;
}

#include "rtos_pub.h" // Required for rtos_delay_milliseconds

// ====================================================================
// OPTIMIZED DASHBOARD FRONTEND (Sequential State Machine Javascript)
// Includes Apple Full-Screen Web App Settings
// ====================================================================
poststr(request,
        "<!DOCTYPE html><html><head>"
        "<meta charset='utf-8'>"
        "<meta name='viewport' content='width=1024, initial-scale=1.0'>"
        "<meta name='apple-mobile-web-app-capable' content='yes'>"
        "<meta name='apple-mobile-web-app-status-bar-style' content='black-translucent'>"
        "<title>My Dashboard</title>"
        "<style>"
        "body{margin:0;background:#000;"
        "display:-webkit-box;display:-webkit-flex;display:flex;"
        "-webkit-box-pack:center;-webkit-justify-content:center;justify-content:center;}"

        "#dash-container{max-width:1024px;width:100%;min-height:100vh;background:#121212;padding:10px 20px 20px;box-sizing:border-box;font-family:-apple-system,sans-serif;color:#eee;position:relative;}"

        ".top-stats{"
        "display:-webkit-box;display:-webkit-flex;display:flex;"
        "-webkit-box-orient:horizontal;-webkit-box-direction:normal;"
        "-webkit-flex-direction:row;flex-direction:row;"
        "-webkit-box-pack:justify;-webkit-justify-content:space-between;justify-content:space-between;"
        "-webkit-box-align:center;-webkit-align-items:center;align-items:center;"
        "background:#222;padding:18px;border-radius:8px;text-align:center;margin-top:15px;width:100%;box-sizing:border-box;white-space:nowrap;}"

        ".top-stats div{"
        "display:-webkit-box;display:-webkit-flex;display:flex;"
        "-webkit-box-orient:vertical;-webkit-box-direction:normal;"
        "-webkit-flex-direction:column;flex-direction:column;"
        "-webkit-box-pack:center;-webkit-justify-content:center;justify-content:center;"
        "margin:0 10px;}"

        ".top-stats label{color:#888;font-size:20px;text-transform:uppercase;margin-bottom:6px;display:block;}"
        ".top-stats b{font-size:38px;font-weight:600;}"
        ".c-exp{color:#4caf50;}.c-imp{color:#f44336;}"

        ".dash-row{"
        "display:-webkit-box;display:-webkit-flex;display:flex;"
        "-webkit-box-orient:horizontal;-webkit-box-direction:normal;"
        "-webkit-flex-direction:row;flex-direction:row;"
        "-webkit-box-align:stretch;-webkit-align-items:stretch;align-items:stretch;"
        "margin-top:15px;}"

        ".left-col{-webkit-box-flex:0;-webkit-flex:0 0 22%;flex:0 0 22%;width:22%;background:#222;padding:10px;border-radius:8px;overflow-y:auto;margin-right:15px;box-sizing:border-box;}"

        ".right-side{"
        "-webkit-box-flex:1;-webkit-flex:1;flex:1;"
        "display:-webkit-box;display:-webkit-flex;display:flex;"
        "-webkit-box-orient:vertical;-webkit-box-direction:normal;"
        "-webkit-flex-direction:column;flex-direction:column;"
        "min-width:0;}"

        ".top-row{"
        "display:-webkit-box;display:-webkit-flex;display:flex;"
        "-webkit-box-orient:horizontal;-webkit-box-direction:normal;"
        "-webkit-flex-direction:row;flex-direction:row;"
        "height:400px;"
        "-webkit-box-align:stretch;-webkit-align-items:stretch;align-items:stretch;}"

        ".sens-tbl{width:100%;font-size:14px;border-collapse:collapse;}"
        ".sens-tbl td{padding:5px 0;border-bottom:1px solid #333;font-weight:normal;}"
        ".sens-tbl td:last-child{font-weight:bold;text-align:right;}"
        ".sens-grp-lbl{font-size:12px;color:#888;text-transform:uppercase;margin:14px 0 8px;}"

        ".graph-col{"
        "-webkit-box-flex:1;-webkit-flex:1;flex:1;"
        "background:#222;padding:15px;border-radius:8px;"
        "display:-webkit-box;display:-webkit-flex;display:flex;"
        "-webkit-box-align:center;-webkit-align-items:center;align-items:center;"
        "-webkit-box-pack:center;-webkit-justify-content:center;justify-content:center;"
        "box-sizing:border-box;margin-right:15px;overflow:hidden;}"

        "canvas{width:100%;height:auto;display:block;margin:0 auto;}"

        ".right-col{-webkit-box-flex:0;-webkit-flex:0 0 23%;flex:0 0 23%;width:23%;background:#222;padding:20px;border-radius:8px;"
        "display:-webkit-box;display:-webkit-flex;display:flex;"
        "-webkit-box-orient:vertical;-webkit-box-direction:normal;"
        "-webkit-flex-direction:column;flex-direction:column;"
        "box-sizing:border-box;}"

        ".btn-tgl{width:100%;height:50px;border:none;color:#fff;border-radius:6px;font-weight:bold;cursor:pointer;font-size:16px;margin-bottom:12px;display:block;}"
        ".sld-v-block{margin-top:10px;width:100%;}"
        ".sld-v-block label{display:block;font-size:11px;color:#888;margin-bottom:6px;text-transform:uppercase;letter-spacing:.5px;}"

        ".bottom-clk-row{"
        "background:#222;border-radius:8px;padding:10px 25px;margin-top:15px;"
        "display:-webkit-box;display:-webkit-flex;display:flex;"
        "-webkit-box-align:center;-webkit-align-items:center;align-items:center;"
        "-webkit-box-pack:center;-webkit-justify-content:center;justify-content:center;"
        "box-sizing:border-box;width:100%;}"

        ".clk-text-wrap{"
        "display:-webkit-box;display:-webkit-flex;display:flex;"
        "-webkit-box-orient:vertical;-webkit-box-direction:normal;"
        "-webkit-flex-direction:column;flex-direction:column;"
        "-webkit-box-align:start;-webkit-align-items:flex-start;align-items:flex-start;"
        "margin-left:20px;text-align:left;}"

        "#d-clk{font-size:120px;font-weight:bold;color:#09F;font-family:monospace;line-height:1;letter-spacing:-3px;}"
        "#d-day{font-size:26px;font-weight:600;color:#eee;text-transform:uppercase;font-family:sans-serif;letter-spacing:2px;margin-bottom:2px;}"
        "#d-date{font-size:16px;color:#888;font-family:sans-serif;}"
        ".close-btn{position:absolute;top:10px;right:15px;font-size:16px;color:#666;cursor:pointer;z-index:10;}"
        ".sep-lbl{font-size:12px;color:#888;margin-bottom:8px;text-transform:uppercase;}"

        ".leg-row{"
        "display:-webkit-box;display:-webkit-flex;display:flex;"
        "-webkit-box-align:center;-webkit-align-items:center;align-items:center;"
        "margin-bottom:10px;}"

        ".leg-swatch{display:inline-block;width:18px;height:4px;margin-right:12px;}"
        ".param-lbl{font-size:12px;color:#888;text-transform:uppercase;margin-top:10px;margin-bottom:5px;}"
        "#c-chg{display:block;font-size:14px;font-weight:normal;color:#4caf50;margin-top:4px;}"
        "</style></head><body>"
    );
    rtos_delay_milliseconds(1);

    // --- CHUNK 2: Core Layout Structure ---
    poststr(request,
        "<div id='dash-container'>"
        "<div class='close-btn' onclick='window.location.href=\"/index\"'>&#x2715;</div>"
        "<div class='top-stats'>"
        "<div><label>Voltage &amp; Current</label><b id='d-va'>--</b></div>"
        "<div><label>Power</label><b id='d-pwr'>--</b></div>"
        "<div><label>Now / 15min Est.</label><b><span id='d-bal'>--</span> / <span id='d-est'>--</span></b></div>"
        "<div id='d-chg-box'><label id='c-lbl'>ESS Status:</label><b id='c-v'>--</b><span id='c-chg'></span></div>"
        "</div>"
    );
    rtos_delay_milliseconds(1);

    // --- CHUNK 3a: Left column (Sensor Data + Energy Totals + Consumption Details + Graph Legend)
    if (CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE)) {
        poststr(request,
            "<div class='dash-row'>"
            "<div class='left-col'>"
            "<div class='sep-lbl'>Sensor Data</div>"
            "<table class='sens-tbl'><tbody>"
            "<tr><td>Power Factor</td><td id='d-pf'>--</td></tr>"
            "</tbody></table>"
            "<div class='sens-grp-lbl'>Energy Totals</div>"
            "<table class='sens-tbl'><tbody>"
            "<tr><td>Consumption</td><td id='d-econs'>--</td></tr>"
            "<tr><td>Generation</td><td id='d-egen'>--</td></tr>"
            "</tbody></table>"
            "<div class='sens-grp-lbl'>Consumption Details</div>"
            "<table class='sens-tbl'><tbody>"
            "<tr><td>Last Hour</td><td id='d-clh'>--</td></tr>"
            "<tr><td>Today</td><td id='d-ctoday'>--</td></tr>"
            "<tr><td>Yesterday</td><td id='d-cyest'>--</td></tr>"
            "<tr><td>2 Days Ago</td><td id='d-c2d'>--</td></tr>"
            "<tr><td>3 Days Ago</td><td id='d-c3d'>--</td></tr>"
            "</tbody></table>"
            "<div style='margin-top:20px;font-size:14px;color:#eee;padding:15px;background:#1a1a1a;border-radius:6px;border:1px solid #333;'>"
            "<div class='sep-lbl' style='margin-bottom:12px;'>Graph Legend</div>"
            "<div class='leg-row'><span class='leg-swatch' style='background:#aaa;'></span><b>Total Energy</b></div>"
            "<div class='leg-row'><span class='leg-swatch' style='background:#4caf50;'></span><b>Charger Avg</b></div>"
            "<div class='leg-row'><span class='leg-swatch' style='background:#ff9800;'></span><b>Inverter Avg</b></div>"
            "</div>"
            "</div>"
            "<div class='right-side'>"
            "<div class='top-row'>"
        );
        rtos_delay_milliseconds(1);

        // --- CHUNK 3b: Graph column, right column ("ESS System Modes")
        poststr(request,
            "<div class='graph-col'>"
            "<div style='width:100%;max-width:592px;margin:0 auto;'>"
            "<div style='position:relative;width:100%;padding-bottom:57.43%;'>"
            "<canvas id='dynCanvas' style='position:absolute;top:0;left:0;width:100%;height:100%;'></canvas>"
            "</div></div></div>"
            "<div class='right-col'>"
            "<div class='sep-lbl'>ESS System Modes</div>"
            "<button id='m-btn' class='btn-tgl' onclick='tm()'>--</button>"
            "<button id='inv-btn' class='btn-tgl' onclick='t_inv()'>INVERTER</button>"
            "<button id='chg-btn' class='btn-tgl' onclick='t_chg()'>CHARGER</button>"
            "<div class='param-lbl'>Parameters</div>"
            "<div class='sld-v-block'>"
            "<label>Max Pwr (<span id='lbl-pwr'></span>%)</label>"
            "<input type='range' id='sld-pwr' min='18' max='100' value='100' onchange='s_pwr(this.value)' style='width:100%;'>"
            "</div>"
            "<div class='sld-v-block' style='margin-top:15px;'>"
            "<label>Export (<span id='lbl-exp'></span> Wh)</label>"
            "<input type='range' id='sld-exp' min='10' max='100' value='20' onchange='s_exp(this.value)' style='width:100%;'>"
            "</div>"
            "</div>"
            "</div>"
            "<div class='bottom-clk-row'>"
            "<div id='d-clk'>--:--</div>"
            "<div class='clk-text-wrap'><div id='d-day'>--</div><div id='d-date'>--</div></div>"
            "</div>"
            "</div>"
            "</div>"
        );
        rtos_delay_milliseconds(1);
    }

    // --- CHUNK 6: Sequential State Machine Javascript ---
    poststr(request,
        "<script>"
        "var busy        = false;"
        "var lastEv      = -1;"
        "var lastEnergyT = 0;"
        "var lastGraphT  = 0;"
        "var graphIdx    = 0;"
        "var lastClk     = '';"
        "var state_net   = [];"
        "var state_chg   = [];"
        "var state_inv   = [];"
        "var GTYPES      = ['net','chg','inv'];"
        "var dmp=0,auto=0;"
        "var DAYS=['SUNDAY','MONDAY','TUESDAY','WEDNESDAY','THURSDAY','FRIDAY','SATURDAY'];"
        "var MOS=['January','February','March','April','May','June','July','August','September','October','November','December'];"

        "function setV(id,v){var e=document.getElementById(id);if(e){if(e.tagName==='INPUT')e.value=v;else e.innerHTML=v;}}"
        "function setC(id,v){var e=document.getElementById(id);if(e)e.className=v;}"
        "function setS(id,v){var e=document.getElementById(id);if(e)e.style.color=v;}"

        "function xhr(url, cb) {"
        "  var r = new XMLHttpRequest();"
        "  r.onreadystatechange = function() {"
        "    if (r.readyState !== 4) return;"
        "    try { cb(r.status === 200 ? JSON.parse(r.responseText) : null); }"
        "    catch(e) { cb(null); }"
        "  };"
        "  r.open('GET', url + '&t=' + Date.now(), true);"
        "  r.send();"
        "}"

        "function s_pwr(v){xhr('/cm?cmnd=SetTargetPower%20'+v,function(){});setV('lbl-pwr',v);}"
        "function s_exp(v){xhr('/cm?cmnd=SetTargetExport%20'+v,function(){});setV('lbl-exp',v);}"
        "function upd(v){if(auto===1)return;if(v>=18){setV('sld-pwr',v);}s_pwr(v);dmp=parseInt(v,10);btnColor();}"
        "function t_inv(){upd(dmp===5?0:5);}"
        "function t_chg(){upd(dmp>=10?0:18);}"
        "function tm(){auto=(auto===1)?0:1;xhr('/cm?cmnd=ToggleAuto',function(){});btnColor();}"
        "function btnColor(){"
        "  var i=document.getElementById('inv-btn'),c=document.getElementById('chg-btn'),m=document.getElementById('m-btn');"
        "  if(i)i.style.background=(dmp===5)?'#ff9800':'#555';"
        "  if(c)c.style.background=(dmp>18)?'#4caf50':((dmp>=10&&dmp<=18)?'#8bc34a':'#555');"
        "  if(m){m.innerHTML=(auto===1)?'AUTO':'MANUAL';m.style.background=(auto===1)?'#09F':'#f44336';}"
        "}"

        "function applyCore(d) {"
        "  setV('d-va',  d.va);"
        "  setV('d-pwr', d.pwr);   setC('d-pwr', d.pwr_cls);"
        "  setV('d-bal', d.bal);   setC('d-bal', d.bal_cls);"
        "  setV('d-est', d.est);   setC('d-est', d.est_cls);"
        "  setV('c-v',   d.chg_v); setS('c-v',   d.chg_c);"
        "  setV('c-chg', (d.dmp >= 18 && d.dmp <= 100) ? 'Charging' : '');"
        "  if (d.clk !== lastClk) { setV('d-clk', d.clk); lastClk = d.clk; }"
        "  if (d.t_pwr >= 18) setV('sld-pwr', d.t_pwr);"
        "  setV('lbl-pwr', d.t_pwr); setV('sld-exp', d.t_exp); setV('lbl-exp', d.t_exp);"
        "  dmp = d.dmp; auto = d.auto; btnColor();"
        "  var dt = new Date();"
        "  setV('d-day',  DAYS[dt.getDay()]);"
        "  setV('d-date', MOS[dt.getMonth()] + ' ' + dt.getDate() + ', ' + dt.getFullYear());"
        "}"

        "function applyEnergy(d) {"
        "  setV('d-pf',     d.pf);     setV('d-econs',  d.econs);"
        "  setV('d-egen',   d.egen);   setV('d-clh',    d.clh);"
        "  setV('d-ctoday', d.ctoday); setV('d-cyest',  d.cyest);"
        "  setV('d-c2d',    d.c2d);    setV('d-c3d',    d.c3d);"
        "  lastEv      = d.ev;"
        "  lastEnergyT = Date.now();"
        "}"

        "function applyGraph(d) {"
        "  if (d.net) state_net = d.net;"
        "  if (d.chg) state_chg = d.chg;"
        "  if (d.inv) state_inv = d.inv;"
        "  renderGraph();"
        "}"

        "function runCycle() {"
        "  if (busy) return;"
        "  busy = true;"
        "  var now = Date.now();"
        "  xhr('/api_dash?req=core', function(d) {"
        "    var needEnergy = false;"
        "    if (d) {"
        "      applyCore(d);"
        "      needEnergy = (d.ev !== undefined) && (d.ev !== lastEv || now - lastEnergyT >= 60000);"
        "    }"
        "    function doGraph() {"
        "      if (now - lastGraphT < 20000) { busy = false; return; }"
        "      xhr('/api_dash?req=' + GTYPES[graphIdx % 3], function(gd) {"
        "        if (gd) { applyGraph(gd); lastGraphT = Date.now(); graphIdx++; }"
        "        busy = false;"
        "      });"
        "    }"
        "    if (needEnergy) {"
        "      xhr('/api_dash?req=energy', function(ed) {"
        "        if (ed) applyEnergy(ed);"
        "        doGraph();"
        "      });"
        "    } else {"
        "      doGraph();"
        "    }"
        "  });"
        "}"

        "function loadAll() {"
        "  busy = true;"
        "  xhr('/api_dash?req=core', function(d) {"
        "    if (d) applyCore(d);"
        "    xhr('/api_dash?req=energy', function(ed) {"
        "      if (ed) applyEnergy(ed);"
        "      xhr('/api_dash?req=net', function(g) {"
        "        if (g) applyGraph(g);"
        "        xhr('/api_dash?req=chg', function(g) {"
        "          if (g) applyGraph(g);"
        "          xhr('/api_dash?req=inv', function(g) {"
        "            if (g) applyGraph(g);"
        "            lastGraphT = Date.now();"
        "            graphIdx   = 0;"
        "            busy       = false;"
        "          });"
        "        });"
        "      });"
        "    });"
        "  });"
        "}"

        "function _buildPath(ctx,p){"
        "ctx.beginPath();ctx.moveTo(p[0].x,p[0].y);"
        "for(var i=0;i<47;i++){"
        "var xc=(p[i].x+p[i+1].x)/2,yc=(p[i].y+p[i+1].y)/2;"
        "ctx.quadraticCurveTo(p[i].x,p[i].y,xc,yc);"
        "}"
        "ctx.lineTo(p[47].x,p[47].y);"
        "}"
        
        "function drawSmooth(ctx,arr,baseY,clamp,fill,col,lw){"
        "if(!arr||arr.length===0)return;"
        "var p=[],h,i;"
        "for(i=0;i<48;i++){"
        "h=(arr[i]||0)/2;"
        "if(clamp){if(h>150)h=150;if(h<-75)h=-75;}"
        "p.push({x:i*11+60,y:baseY-h});"
        "}"
        "if(fill){"
        "_buildPath(ctx,p);"
        "ctx.lineTo(577,baseY);ctx.lineTo(60,baseY);"
        "ctx.fillStyle=fill;ctx.fill();"
        "}"
        "_buildPath(ctx,p);"
        "ctx.strokeStyle=col;ctx.lineWidth=lw;ctx.stroke();"
        "ctx.beginPath();ctx.arc(p[47].x,p[47].y,lw*1.5,0,2*Math.PI);"
        "ctx.fillStyle=col;ctx.fill();"
        "}"

        "var gridCanvas=null;"
        "function initGrid(){"
        "var gc=document.createElement('canvas');"
        "var r=window.devicePixelRatio||1;"
        "gc.width=Math.round(592*r);gc.height=Math.round(340*r);"
        "var ctx=gc.getContext('2d');"
        "ctx.scale(r,r);"
        "ctx.fillStyle='#181818';"
        "ctx.fillRect(60,10,517,50);ctx.fillRect(60,75,517,235);"
        "ctx.lineWidth=1;ctx.strokeStyle='#333';ctx.beginPath();"
        "ctx.moveTo(60,35);ctx.lineTo(577,35);"
        "ctx.moveTo(60,75);ctx.lineTo(577,75);"
        "ctx.moveTo(60,150);ctx.lineTo(577,150);"
        "ctx.moveTo(60,300);ctx.lineTo(577,300);ctx.stroke();"
        "ctx.strokeStyle='#444';ctx.beginPath();"
        "ctx.moveTo(60,60);ctx.lineTo(577,60);"
        "ctx.moveTo(60,225);ctx.lineTo(577,225);ctx.stroke();"
        "ctx.strokeStyle='#666';ctx.beginPath();"
        "ctx.moveTo(60,10);ctx.lineTo(60,60);"
        "ctx.moveTo(60,75);ctx.lineTo(60,310);"
        "ctx.moveTo(577,10);ctx.lineTo(577,60);"
        "ctx.moveTo(577,75);ctx.lineTo(577,310);ctx.stroke();"
        "ctx.fillStyle='#aaa';ctx.font='14px sans-serif';ctx.textAlign='right';ctx.textBaseline='middle';"
        "ctx.fillText('100',48,10);ctx.fillText('0',48,60);"
        "ctx.fillText('+300',48,75);ctx.fillText('+150',48,150);"
        "ctx.fillStyle='#ccc';ctx.fillText('0 Wh',48,225);"
        "ctx.fillStyle='#aaa';ctx.fillText('-150',48,300);"
        "ctx.lineWidth=1;ctx.beginPath();ctx.font='12px sans-serif';ctx.textBaseline='top';"
        "for(var i=0;i<=47;i++){"
        "var x=(47-i)*11+60;ctx.moveTo(x,310);"
        "if(i%4===0){"
        "ctx.lineTo(x,316);ctx.textAlign=(i===0)?'right':'center';"
        "ctx.fillText((i===0)?'Now':'-'+(i/4)+'h',x,320);"
        "}else{ctx.lineTo(x,313);}"
        "}"
        "ctx.stroke();"
        "gridCanvas=gc;"
        "}"

        "function renderGraph(){"
        "var c=document.getElementById('dynCanvas');"
        "if(!c||!c.getContext)return;"
        "var ctx=c.getContext('2d');"
        "var r=window.devicePixelRatio||1;"
        "c.width=Math.round(592*r);c.height=Math.round(340*r);"
        "ctx.scale(r,r);"
        "ctx.clearRect(0,0,592,340);"
        "if(gridCanvas)ctx.drawImage(gridCanvas,0,0,592,340);"
        "if(state_net.length>0){"
        "var grad=ctx.createLinearGradient(0,75,0,310);"
        "grad.addColorStop(0,'rgba(244,67,54,.5)');"
        "grad.addColorStop(.638,'rgba(244,67,54,.15)');"
        "grad.addColorStop(.638,'rgba(76,175,80,.15)');"
        "grad.addColorStop(1,'rgba(76,175,80,.5)');"
        "drawSmooth(ctx,state_net,225,true,grad,'#aaa',2.5);"
        "}"
        "if(state_chg.length>0)drawSmooth(ctx,state_chg,60,false,null,'#4caf50',2.5);"
        "if(state_inv.length>0)drawSmooth(ctx,state_inv,60,false,null,'#ff9800',2.5);"
        "}"

        "initGrid(); loadAll(); setInterval(runCycle, 10000);"
        "</script></body></html>"
    );

    poststr(request, NULL);
    return 0;
}

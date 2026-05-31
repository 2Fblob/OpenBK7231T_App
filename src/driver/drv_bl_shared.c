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
int current_minute = 0;
int last_minute = 0;
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
    const char *mode;
    struct tm *ltm;

    if(DRV_IsRunning("BL0937")) { mode = "BL0937"; } 
    else if(DRV_IsRunning("BL0942")) { mode = "BL0942"; } 
    else if (DRV_IsRunning("BL0942SPI")) { mode = "BL0942SPI"; } 
    else if(DRV_IsRunning("CSE7766")) { mode = "CSE7766"; } 
    else if(DRV_IsRunning("RN8209")) { mode = "RN8209"; } 
    else { mode = "PWR"; }

   // ====================================================================
    // UI DASHBOARD & CSS
    // ====================================================================
    poststr(request, "<style>");
    poststr(request, "#state { display: flex; flex-direction: column; }");
    poststr(request, "#my-dash { order: -1; width: 100%; }"); 
    
    poststr(request, ".my-tbl { width:100%; text-align:center; font-size:16px; margin:10px 0; table-layout:fixed; }");
    poststr(request, ".my-tbl th { color:#aaa; font-weight:normal; padding-bottom:5px; border-bottom:1px solid #444; }");
    poststr(request, ".my-tbl td { padding-top:10px; padding-bottom:10px; }");
    
    poststr(request, ".dash-row { display:flex; justify-content:space-between; flex-wrap:wrap; margin-top:20px; text-align:left; gap:20px;}");
    
    // Graph CSS: Exactly 480x201. 32 bars * 15px = 480px.
    poststr(request, ".g-wrap { display:flex; height:201px; width:480px; background:#222; border-radius:4px; font-family:sans-serif; margin-top:10px; overflow:hidden;}");
    poststr(request, ".g-b { width:15px; height:100%; display:flex; flex-direction:column; }");
    
    // The perfect 1px zero line is created safely by a bottom border on the top half
    poststr(request, ".g-top { height:61px; position:relative; border-bottom:1px solid #999; box-sizing:border-box; }");
    poststr(request, ".g-bot { height:140px; position:relative; }");
    
    // Overflow:hidden stops the text from breaking the bar widths
    poststr(request, ".g-up { position:absolute; bottom:0; width:100%; background:#2ecc71; overflow:hidden; display:flex; align-items:flex-end; justify-content:center; }");
    poststr(request, ".g-dn { position:absolute; top:0; width:100%; background:#e74c3c; overflow:hidden; display:flex; align-items:flex-start; justify-content:center; }");
    poststr(request, ".b-txt { color:#fff; font-size:9px; font-weight:bold; writing-mode:vertical-rl; transform:rotate(180deg); padding:2px 0; }");
    poststr(request, "</style>");
    
    poststr(request, "<div id='my-dash'>"); // Open Dashboard Wrapper
  
    // ====================================================================
    // 1. HORIZONTAL DASHBOARD (Top Row)
    // ====================================================================
    poststr(request, "<table class='my-tbl'><tr>");
    poststr(request, "<th>Voltage</th><th>Power</th><th>15-Min Est.</th><th>Charger C</th><th>Status</th></tr><tr>");
    
    hprintf255(request, "<td><b>%.0f V</b></td><td><b>%.0f W</b></td><td><b>%i Wh</b></td><td><b style='color:#0099FF;'>%i%%</b></td><td><b>%s</b></td></tr></table>", 
               sensors[OBK_VOLTAGE].lastReading, sensors[OBK_POWER].lastReading, estimated_energy_period, dump_load_relay[5], solar_available ? "Exporting" : "Importing");

    if (CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE) && NTP_IsTimeSynced())
    {
        minutes_since_midnight = NTP_GetHour() * 60 + NTP_GetMinute();
        int current_interval_of_day = minutes_since_midnight / net_metering_period;
        
poststr(request, "<div class='dash-row'>");

        // ====================================================================
        // 2. THE 480x201 BAR GRAPH (LAST 8 HOURS / 32 BARS) - Left Column
        // ====================================================================
        poststr(request, "<div style='flex:0 0 480px;'>");
        poststr(request, "<h2 style='font-size:18px; margin:0;'>Energy Stats (Last 8 Hours)</h2>");
        poststr(request, "<div class='g-wrap'>");

        // Draw 32 vertical slots (15px each = 480px total)
        for (int i = 31; i >= 0; i--) {
            int interval_of_day = current_interval_of_day - i;
            if (interval_of_day < 0) { interval_of_day += 96; } 
            int c_index = interval_of_day % 32;
            
            int v = net_matrix[c_index];
            if (i == 0) { v += (int)(real_consumption - real_export); } // Add live
            
            poststr(request, "<div class='g-b'>");
            
            if (v < 0) {
                // Export (Green, grows UP). Math: (value * 60px max) / 300W scale
                int h = (abs(v) * 60) / 300;
                if (h > 60) h = 60;
                if (h < 1) h = 1;
                hprintf255(request, "<div class='g-top'><div class='g-up' style='height:%dpx;'><span class='b-txt'>%d</span></div></div><div class='g-bot'></div>", h, abs(v));
            } else if (v > 0) {
                // Import (Red, grows DOWN). Math: (value * 140px max) / 700W scale
                int h = (v * 140) / 700;
                if (h > 140) h = 140;
                if (h < 1) h = 1;
                hprintf255(request, "<div class='g-top'></div><div class='g-bot'><div class='g-dn' style='height:%dpx;'><span class='b-txt'>%d</span></div></div>", h, v);
            } else {
                // Zero
                poststr(request, "<div class='g-top'></div><div class='g-bot'></div>");
            }
            poststr(request, "</div>");
        }
        poststr(request, "</div></div>");

        // ====================================================================
        // 3. DETAILED SENSORS - Right Column
        // ====================================================================
        poststr(request, "<div style='flex:1; min-width:250px;'>");
        poststr(request, "<h3 style='font-size:16px; margin:0 0 10px 0;'>Detailed Sensor Data</h3>");
        poststr(request, "<table style='width:100%; text-align:left; font-size:14px; line-height:1.5;'>");

        for (int i = (OBK__FIRST); i <= (OBK_CONSUMPTION__DAILY_LAST); i++) {
            if (i == OBK_GENERATION_TOTAL && (!CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE))){i++;}
            if (i <= OBK__NUM_MEASUREMENTS || NTP_IsTimeSynced()) {
                
                if (i == OBK_VOLTAGE || i == OBK_POWER) continue; // Skip redundant items

                poststr(request, "<tr><td style='border-bottom:1px solid #333;'><b>");
                poststr(request, sensors[i].names.name_friendly);
                poststr(request, "</b></td><td style='text-align:right; border-bottom:1px solid #333;'>");
                
                if ((i == OBK_CONSUMPTION_TOTAL) || (i == OBK_GENERATION_TOTAL)) {
                    hprintf255(request, "%.*f kWh</td></tr>", sensors[i].rounding_decimals, (0.001*sensors[i].lastReading));
                } else {
                    hprintf255(request, "%.*f %s</td></tr>", sensors[i].rounding_decimals, sensors[i].lastReading, sensors[i].names.units);
                }
            }
        };
        poststr(request, "</table></div>");
        poststr(request, "</div>"); // Close dash-row
    }
    
    poststr(request, "</div><br>"); // Close my-dash
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
        
        // Maps the interval to our expanded 32-slot circular buffer
        int current_matrix_index = interval_of_day_tracker % 32; 

        if (last_matrix_index == -1) {
            last_matrix_index = current_matrix_index;
        }

        if (current_matrix_index != last_matrix_index) {
            
            // 1. Write the final accumulated values to the outgoing slot
            consumption_matrix[last_matrix_index] = (int)real_consumption;
            export_matrix[last_matrix_index] = (int)real_export;
            net_matrix[last_matrix_index] = (int)real_consumption - (int)real_export;

            // 2. Clear variables for the new period
            real_export = 0;
            real_consumption = 0;
            net_energy = 0;
            energyCounterMinutesIndex = 0;
            lastsync = 0; 
            
            // Wipe the incoming block 
            consumption_matrix[current_matrix_index] = 0;
            export_matrix[current_matrix_index] = 0;
            net_matrix[current_matrix_index] = 0;

            // 3. Update index and flag
            last_matrix_index = current_matrix_index;
            savetoflash = 1;

            // Reset loop commands
            last_dump_load_relay[0] = 2;
            last_dump_load_relay[1] = 2;
            last_dump_load_relay[2] = 2;
            last_dump_load_relay[3] = 2;
            last_dump_load_relay[4] = 2;
            last_dump_load_relay[5] = 2;
        }
        // ------------------------------------------------------------------------------------------------------

        if (!(check_time == old_time))
        {
            min_reset = 1;
            old_time = check_time;
            lastsync++;
        }
                                                 
        net_energy = (real_consumption - real_export);                                

        // ** Storage inverter control (Index 0)**
        if (net_energy < -100) {
            solar_available = 1; 
        } else if (net_energy > 10) {
            solar_available = 0; 
        }
        
        if (solar_available == 0) {
            if (net_energy > 0) {
                dump_load_relay[0] = 1; 
            } else if (net_energy <= -10) {
                dump_load_relay[0] = 0; 
            }
        } else if (solar_available == 1) {
            if (net_energy > 50) {
                dump_load_relay[0] = 1; 
            } else if (net_energy <= 0) {
                dump_load_relay[0] = 0; 
            }
        }
        
        current_minute = check_time;
        
        if (current_minute != last_minute) 
        {
            last_minute = current_minute;
            
            int min_in_block = current_minute % 15; 
            int check_time_estimate_mins = 15 - min_in_block; 
            
            estimated_energy_period = (int)net_energy + ((int)sensors[OBK_POWER].lastReading * check_time_estimate_mins) / 60;
            int projected_power_w = estimated_energy_period * 4;
            int current_net_power_w = ((int)net_energy) * 4;

            if (min_in_block > 0) {
                net_energy_equivalent = (int)((float)net_energy * (15.0f / min_in_block));                                                
            } else {
                net_energy_equivalent = (int)net_energy; 
            }

            // ** Charger C PWM (Index 5) **
            int scaled_power;
            
            if (projected_power_w > 50) { 
                scaled_power = -5; 
            } 
            else if (projected_power_w < -950) { 
                scaled_power = 100; 
            } 
            else { 
                scaled_power = ((50 - projected_power_w) * 100) / 1000;         
                if (scaled_power >= 1 && scaled_power <= 10) {scaled_power = 10;} 
            }
            
            int change = scaled_power - 5;

            if (current_net_power_w > 0) {
                dump_load_relay[5] = (current_net_power_w / 10 > 5) ? 5 : (current_net_power_w / 10);  
            } 
            else if (current_net_power_w == 0) {
                dump_load_relay[5] = 0;  
            } 
            else if (change != 0) { 
                if (current_net_power_w <= -50 || (dump_load_relay[5] > 5 && change < 0)) {
                    dump_load_relay[5] += change;
                }
                if (dump_load_relay[5] < 10) {dump_load_relay[5] = 10;}
            }
            
            dump_load_relay[5] = (dump_load_relay[5] > 100) ? 100 : (dump_load_relay[5] < 0 ? 0 : dump_load_relay[5]);

            if (current_net_power_w < 0 && current_net_power_w > -51) {
                dump_load_relay[5] = 10;  
            }
        
            // ** External Relays (Indices 1, 2, 3, 4) **
            if (min_in_block > 13) 
            {
                // Primary Charger (Index 1)
                dump_load_relay[1] = (net_energy_equivalent <= -50 && check_hour >= 8 && check_hour <= 17) ? 1 : 
                                     ((net_energy >= -12) ? 0 : dump_load_relay[1]);
                
                // Secondary Charger (Index 3)
                dump_load_relay[3] = (net_energy_equivalent <= -125 && check_hour >= 9 && check_hour <= 15) ? 1 : 
                                     (( net_energy >= -25) ? 0 : dump_load_relay[3]);                                  
        
                // Basement Dehumidifier (Index 4)
                if (((check_time >= 40 && check_time <= 58 && net_energy_equivalent <= -50) && (check_hour >= 8 && check_hour <= 13))||(check_hour == 14 || check_hour == 16)) {
                    dump_load_relay[4] = 1; 
                } else if (min_in_block == 14 || net_energy >= -2) {
                    dump_load_relay[4] = 0; 
                }
        
                // Dishwasher (Index 2)
                if ((net_energy_equivalent <= -175) && (check_hour >= 9 && check_hour <= 18)) {
                    dump_load_relay[2] = 1; 
                } else if (net_energy >= 75) {
                    dump_load_relay[2] = 0; 
                }
            }
                                                     
            for (int output_index = 0; output_index < dump_load_relay_number; output_index++) 
            {
                if ((check_hour == 0) && (check_time == 0)) {
                    dump_load_relay_timer[output_index] = 0;
                } else {
                    if (dump_load_relay[output_index] > 0) { 
                        dump_load_relay_timer[output_index]++;
                    }
                }
            }

            // Command Execution Block
            for (int output_index = 0; output_index < dump_load_relay_number; output_index++) 
            {
                if (dump_load_relay[output_index] != last_dump_load_relay[output_index]) 
                {
                    update_number = output_index;
                    last_dump_load_relay[output_index] = dump_load_relay[output_index];
            
                    char output_command[64] = "";
                    const char *ip_start = "SendGet http://192.168.8.";
                    const char *ip_middle = "/cm?cmnd=Power%20"; 

                    if (dump_load_relay_ip[output_index] == charger_c_ip) 
                    {
                        ip_middle = "/cm?cmnd=Channel3%20";  
                        if (dump_load_relay[output_index] < 5) { old_output = -dump_load_relay[output_index]; } 
                        else { old_output = dump_load_relay[output_index]; } 
                    }
            
                    snprintf(output_command, sizeof(output_command), "%s%d%s%d", ip_start, dump_load_relay_ip[output_index], ip_middle, dump_load_relay[output_index]);
                    CMD_ExecuteCommand(output_command, 0);
                    
                    break;
                }
            }
        }
    } // end of negative flag loop

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

    CMD_RegisterCommand("EnergyCntReset", BL09XX_ResetEnergyCounter, NULL);
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

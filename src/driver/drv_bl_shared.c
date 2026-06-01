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
    // UI DASHBOARD & MINIMAL CSS
    // ====================================================================
    poststr(request, "<style>");
    poststr(request, "#state { display: flex; flex-direction: column; }");
    poststr(request, "#my-dash { order: -1; width: 100%; box-sizing: border-box; }"); 
    
    poststr(request, ".my-tbl { width:100%; text-align:center; font-size:16px; margin:10px 0; table-layout:fixed; border-collapse:collapse; }");
    poststr(request, ".my-tbl th { color:#aaa; font-weight:normal; padding-bottom:5px; border-bottom:1px solid #444; }");
    poststr(request, ".my-tbl td { padding-top:10px; padding-bottom:10px; }");
    
    poststr(request, ".dash-row { display:flex; flex-wrap:wrap; gap:20px; margin-top:20px; align-items:flex-start; }");
    
    poststr(request, ".sens-tbl { width:100%; text-align:left; font-size:14px; line-height:1.8; white-space:nowrap; border-collapse:collapse; }");
    poststr(request, ".sens-tbl td { border-bottom:1px solid #333; }");
    poststr(request, "</style>");
    
    poststr(request, "<div id='my-dash'>"); 

    // ====================================================================
    // 1. HORIZONTAL DASHBOARD (Top Row)
    // ====================================================================
    poststr(request, "<table class='my-tbl'><tr>");
    poststr(request, "<th>Voltage</th><th>Power</th><th>15-Min Est.</th><th>Charger C</th><th>Status</th></tr><tr>");
    
    hprintf255(request, "<td><b>%.0f V</b></td><td><b>%.0f W</b></td><td><b>%i Wh</b></td><td><b style='color:#0099FF;'>%i%%</b></td><td><b>%s</b></td></tr></table>", 
               sensors[OBK_VOLTAGE].lastReading, 
               sensors[OBK_POWER].lastReading, 
               estimated_energy_period, 
               dump_load_relay[5], 
               (sensors[OBK_POWER].lastReading < 0) ? "Exporting" : "Importing");

    if (CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE) && NTP_IsTimeSynced())
    {
        minutes_since_midnight = NTP_GetHour() * 60 + NTP_GetMinute();
        int current_interval_of_day = minutes_since_midnight / net_metering_period;
        
        poststr(request, "<div class='dash-row'>");

        // ====================================================================
        // 2. THE SVG BAR GRAPH (LAST 8 HOURS / 32 BARS) - Left Column
        // ====================================================================
        poststr(request, "<div style='flex:1; min-width:300px; overflow-x:auto;'>"); 
        poststr(request, "<h2 style='font-size:18px; margin:0 0 10px 0;'>Energy Stats (Last 8 Hours)</h2>");
        
        poststr(request, "<svg width='480' height='300' viewBox='0 0 480 300' style='background:transparent; border:1px solid #999; border-radius:0px;'>");
        poststr(request, "<line x1='0' y1='90' x2='480' y2='90' stroke='#999' stroke-width='1' />");

        poststr(request, "<text x='5' y='12' fill='#999' font-size='10'>-300</text>");
        poststr(request, "<text x='5' y='86' fill='#999' font-size='10'>0</text>");
        poststr(request, "<text x='5' y='295' fill='#999' font-size='10'>+700</text>");

        for (int i = 31; i >= 0; i--) {
            int interval_of_day = current_interval_of_day - i;
            if (interval_of_day < 0) { interval_of_day += 96; } 
            int c_index = interval_of_day % 32;
            
            int v = net_matrix[c_index];
            if (i == 0) { v += (int)(real_consumption - real_export); } 
            
            int x_pos = (31 - i) * 15 + 2; 
            
            if (v < 0) {
                int h = (abs(v) * 90) / 300;
                if (h > 90) h = 90;
                if (h < 1) h = 1;
                int y_rect = 90 - h;
                
                hprintf255(request, 
                    "<rect x='%d' y='%d' width='11' height='%d' fill='#2ecc71'/>"
                    "<text x='%d' y='%d' font-size='9' fill='#ccc' transform='rotate(-90,%d,%d)'>%d</text>", 
                    x_pos, y_rect, h, 
                    x_pos + 8, y_rect - 3, x_pos + 8, y_rect - 3, abs(v));
            } else if (v > 0) {
                int h = (v * 210) / 700;
                if (h > 210) h = 210;
                if (h < 1) h = 1;
                
                hprintf255(request, 
                    "<rect x='%d' y='90' width='11' height='%d' fill='#e74c3c'/>"
                    "<text x='%d' y='%d' font-size='9' fill='#ccc' transform='rotate(-90,%d,%d)'>%d</text>", 
                    x_pos, h, 
                    x_pos + 8, 90 + h + 5, x_pos + 8, 90 + h + 5, v);
            }
        }
        poststr(request, "</svg></div>");

        // ====================================================================
        // 3. DETAILED SENSORS - Right Column
        // ====================================================================
        poststr(request, "<div style='width:260px; flex-shrink:0;'>"); 
        poststr(request, "<h3 style='font-size:16px; margin:0 0 10px 0;'>Detailed Sensor Data</h3>");
        poststr(request, "<table class='sens-tbl'>");

        for (int i = (OBK__FIRST); i <= (OBK_CONSUMPTION__DAILY_LAST); i++) {
            if (i == OBK_GENERATION_TOTAL && (!CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE))){i++;}
            if (i <= OBK__NUM_MEASUREMENTS || NTP_IsTimeSynced()) {
                
                if (i == OBK_VOLTAGE || i == OBK_POWER) continue; // Skip redundant items

                poststr(request, "<tr><td><b>");
                poststr(request, sensors[i].names.name_friendly);
                poststr(request, "</b></td><td style='text-align:right;'>");
                
                if ((i == OBK_CONSUMPTION_TOTAL) || (i == OBK_GENERATION_TOTAL)) {
                    hprintf255(request, "%.*f kWh</td></tr>", sensors[i].rounding_decimals, (0.001*sensors[i].lastReading));
                } else {
                    hprintf255(request, "%.*f %s</td></tr>", sensors[i].rounding_decimals, sensors[i].lastReading, sensors[i].names.units);
                }
            }
        };
        poststr(request, "</table></div>");
        poststr(request, "</div>"); 
    }
    
    poststr(request, "</div><br>"); 
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
        role = g_cfg.pins.roles

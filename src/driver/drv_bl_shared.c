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
    const char *mode;
    unsigned int minutes_since_midnight;

    if(DRV_IsRunning("BL0937")) { mode = "BL0937"; } 
    else if(DRV_IsRunning("BL0942")) { mode = "BL0942"; } 
    else if (DRV_IsRunning("BL0942SPI")) { mode = "BL0942SPI"; } 
    else if(DRV_IsRunning("CSE7766")) { mode = "CSE7766"; } 
    else if(DRV_IsRunning("RN8209")) { mode = "RN8209"; } 
    else { mode = "PWR"; }

    // ====================================================================
    // STYLESHEET DEFINITIONS
    // ====================================================================
    poststr(request, "<style>");
    poststr(request, "body { margin: 0; background-color: #000; }");
    poststr(request, "#my-dash { position: absolute; top: 0; left: 0; width: 100%; min-height: 100vh; background-color: #121212; z-index: 99999; padding: 10px; box-sizing: border-box; font-family: -apple-system, sans-serif; color: #eee; }"); 
    
    // Top Stats Bar
    poststr(request, ".top-stats { display: flex; justify-content: space-between; align-items: center; background: #222; padding: 18px; border-radius: 8px; text-align: center; gap: 5px; }");
    poststr(request, ".top-stats div { display: flex; flex-direction: column; justify-content: center; }");
    poststr(request, ".top-stats span { color: #888; font-size: 25px; text-transform: uppercase; margin-bottom: 6px; display: block; white-space: nowrap; }");
    poststr(request, ".top-stats b { font-size: 29px; font-weight: 600; }");
    
    poststr(request, ".c-exp { color: #4caf50; }");
    poststr(request, ".c-imp { color: #f44336; }");

    // Main Row Containers
    poststr(request, ".dash-row { display: flex; flex-direction: row; gap: 15px; margin-top: 15px; height: 290px; align-items: stretch; }"); 
    poststr(request, ".left-col { flex: 0 0 210px; background: #222; padding: 10px; border-radius: 8px; overflow-y: auto; }");
    poststr(request, ".sens-tbl { width: 100%; font-size: 12px; border-collapse: collapse; }");
    poststr(request, ".sens-tbl td { padding: 5px 0; border-bottom: 1px solid #333; }");

    // Graph Area & Control Column Designations
    poststr(request, ".graph-col { flex: 1; background: #222; padding: 10px; border-radius: 8px; display: flex; flex-direction: column; align-items: center; justify-content: center; overflow: hidden; }");
    poststr(request, ".ctrl-col { flex: 0 0 100px; background: #222; padding: 10px; border-radius: 8px; display: flex; flex-direction: column; align-items: stretch; gap: 10px; box-sizing: border-box; }");
    poststr(request, ".btn-tgl { width: 100%; border: none; color: white; padding: 8px 0; border-radius: 4px; font-weight: bold; cursor: pointer; font-size: 12px; text-align: center; line-height: 1.1; }");
    
    // Bottom Section Layout Rules
    poststr(request, ".hist-tbl-wrapper { flex: 1; min-width: 180px; }");
    poststr(request, ".hist-tbl { width: 100%; text-align: center; font-size: 20px; border-collapse: collapse; }");
    poststr(request, ".hist-tbl th { color: #888; font-weight: normal; padding-bottom: 6px; border-bottom: 1px solid #444; }");
    poststr(request, ".hist-tbl td { padding: 10px 2px; border-bottom: 1px solid #333; }");
    
    poststr(request, ".close-btn { position: absolute; top: 10px; right: 15px; font-size: 16px; color: #666; cursor: pointer; }");
    poststr(request, "</style>");
    
    poststr(request, 
        "<div id='my-dash'>"
        "<div class='close-btn' onclick='document.getElementById(\"my-dash\").style.display=\"none\"'>✕</div>"
    );

    // ====================================================================
    // 1. TOP DASHBOARD ROW
    // ====================================================================
    poststr(request, "<div class='top-stats'>");
    
    // V/A Tracker (~60 bytes total payload)
    hprintf255(request, "<div><span>V / A</span><b id='d-va'>%.0fV / %.2fA</b></div>", sensors[OBK_VOLTAGE].lastReading, sensors[OBK_CURRENT].lastReading);
    
    // Power, Est, and Balance Tracker (~219 bytes total payload - well under 255 buffer limit)
    const char* pwr_cls = (sensors[OBK_POWER].lastReading < 0) ? "c-exp" : "c-imp";
    const char* est_cls = (estimated_energy_period < 0) ? "c-exp" : "c-imp";
    const char* bal_cls = (sensors[OBK_POWER_REACTIVE].lastReading < 0) ? "c-exp" : "c-imp";
    hprintf255(request, 
        "<div><span>Power</span><b id='d-pwr' class='%s'>%.0f W</b></div>"
        "<div><span>Est / Bal</span><b><span id='d-est' class='%s'>%i Wh</span> / <span id='d-bal' class='%s'>%.0f Wh</span></b></div>", 
        pwr_cls, sensors[OBK_POWER].lastReading,
        est_cls, estimated_energy_period, 
        bal_cls, sensors[OBK_POWER_REACTIVE].lastReading);

    // Dynamic Charger Display Logic
    if (dump_load_relay[5] == 0) {
        poststr(request, "<div id='d-chg-box'><span id='c-lbl'>Charger</span><b id='c-v' style='color:#888;'>Idle</b></div>");
    } else if (dump_load_relay[5] == 5) {
        poststr(request, "<div id='d-chg-box'><span id='c-lbl'>Charger</span><b id='c-v' style='color:#4caf50;'>Battery</b></div>");
    } else {
        hprintf255(request, "<div id='d-chg-box'><span id='c-lbl'>Charging</span><b id='c-v' style='color:#0099FF;'>%d%%</b></div>", dump_load_relay[5]);
    }
    
    poststr(request, "</div>");

    if (CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE) && NTP_IsTimeSynced())
    {
        minutes_since_midnight = NTP_GetHour() * 60 + NTP_GetMinute();
        int current_interval_of_day = minutes_since_midnight / net_metering_period;
        
        // BEGINNING OF MAIN GRID MATRIX
        poststr(request, "<div class='dash-row'>");

        // ====================================================================
        // 2. SENSOR COLUMN (Left Alignment Container)
        // ====================================================================
        poststr(request, 
            "<div class='left-col'>"
            "<div style='font-size:12px; color:#888; margin-bottom:8px; text-transform:uppercase;'>Sensor Data</div>"
            "<table class='sens-tbl'><tbody id='d-sens-body'>"
        );

        for (int i = (OBK__FIRST); i <= (OBK_CONSUMPTION__DAILY_LAST); i++) {
            if (i == OBK_GENERATION_TOTAL && (!CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE))){i++;}
            if (i <= OBK__NUM_MEASUREMENTS || NTP_IsTimeSynced()) {
                if (i == OBK_VOLTAGE || i == OBK_POWER || i == OBK_CURRENT || i == OBK_POWER_APPARENT || i == OBK_POWER_REACTIVE) continue; 

                // Compressed table row generation into a single call per iteration
                if ((i == OBK_CONSUMPTION_TOTAL) || (i == OBK_GENERATION_TOTAL)) {
                    hprintf255(request, "<tr><td><b>%s</b></td><td style='text-align:right;'>%.*f kWh</td></tr>", 
                               sensors[i].names.name_friendly, sensors[i].rounding_decimals, (0.001*sensors[i].lastReading));
                } else {
                    hprintf255(request, "<tr><td><b>%s</b></td><td style='text-align:right;'>%.*f %s</td></tr>", 
                               sensors[i].names.name_friendly, sensors[i].rounding_decimals, sensors[i].lastReading, sensors[i].names.units);
                }
            }
        };
        poststr(request, "</tbody></table></div>");
        
        // ====================================================================
        // 3. GRAPH COLUMN (Center Vector Block)
        // ====================================================================
        poststr(request, 
            "<div class='graph-col' id='d-graph'>"
            "<svg viewBox='0 0 512 260' style='width:100%%; height:100%%; background:transparent;'>"
            "<line x1='0' y1='130' x2='512' y2='130' stroke='#333' stroke-width='1'/>"
        );
        
        for (int i = 31; i >= 0; i--) {
            int interval_of_day = (minutes_since_midnight / net_metering_period - i + 96) % 96;
            int v = net_matrix[interval_of_day % 32];
            if (i == 0) { v += (int)(real_consumption - real_export); }
            
            int x = (31 - i) * 16;
            int h = abs(v) / 2;
            if (h > 120) h = 120; // Structural constraint map boundary
            
            if (v != 0 || i == 0) {
                const char* color = (v >= 0) ? "#d32f2f" : "#388e3c";
                int rect_y = (v >= 0) ? (130 - h) : 130;
                int text_y = (v >= 0) ? (130 - h - 6) : (130 + h + 14);
                
                if (h > 0) {
                    hprintf255(request, "<rect x='%d' y='%d' width='15' height='%d' fill='%s' rx='1'/>", x, rect_y, h, color);
                }
                hprintf255(request, "<text x='%d' y='%d' fill='#ddd' font-size='11' font-family='sans-serif' text-anchor='middle'>%d</text>", x + 7, text_y, v);
            } else {
                hprintf255(request, "<text x='%d' y='135' fill='#555' font-size='11' font-family='sans-serif' text-anchor='middle'>0</text>", x + 7);
            }
        }
        poststr(request, "</svg></div>");

        // ====================================================================
        // 4. CONTROL INTERFACE ARRAY (Right Column)
        // ====================================================================
        int dmp = dump_load_relay[5];
        const char* inv_color = (dmp == 5) ? "#4caf50" : "#555555";
        const char* chg_color = (dmp > 18) ? "#4caf50" : ((dmp >= 10 && dmp <= 18) ? "#ffeb3b" : "#555555");
        const char* chg_30_color = (dmp >= 30) ? "#4caf50" : "#555555";
        const char* chg_80_color = (dmp >= 80) ? "#4caf50" : "#555555";
        const char* auto_color = charger_c_auto ? "#0099FF" : "#f44336";
        const char* auto_text = charger_c_auto ? "AUTO" : "MANUAL";

        poststr(request, 
            "<div class='ctrl-col'>"
            "<div style='font-size:10px; color:#888; text-transform:uppercase; text-align:center;'>Controls</div>"
        );
        
        hprintf255(request, "<button id='m-btn' class='btn-tgl' style='background:%s;' onclick='tm()'>%s</button>", auto_color, auto_text);
        hprintf255(request, "<button id='inv-btn' class='btn-tgl' style='background:%s;' onclick='t_inv()'>INVERTER</button>", inv_color);
        hprintf255(request, "<button id='chg-btn' class='btn-tgl' style='background:%s;' onclick='t_chg()'>CHARGER</button>", chg_color);
        
        poststr(request, "<div style='display:flex; gap:4px; width:100%%; margin-top:auto;'>");
        hprintf255(request, "<button id='chg-30-btn' class='btn-tgl' style='background:%s; flex:1; font-size:11px; padding:4px 0;' onclick='upd(30)'>30%%</button>", chg_30_color);
        hprintf255(request, "<button id='chg-80-btn' class='btn-tgl' style='background:%s; flex:1; font-size:11px; padding:4px 0;' onclick='upd(80)'>80%%</button>", chg_80_color);
        poststr(request, "</div></div></div>"); // Close internal divs and dash-row

        // ====================================================================
        // 5. HOURLY DATA TABLE & LARGE CLOCK SYSTEM
        // ====================================================================
        poststr(request, 
            "<div style='display:flex; width:100%%; margin-top:20px; gap:20px; align-items:stretch;'>"
            "<div class='hist-tbl-wrapper'>"
            "<table class='hist-tbl'><tbody id='d-hist-body'>"
            "<tr><th>Time</th><th>Import / Export</th><th>Net</th></tr>"
        );

        for (int i = 0; i < 4; i++) {
            int interval_of_day = current_interval_of_day - i;
            if (interval_of_day < 0) { interval_of_day += 96; } 
            int c_index = interval_of_day % 32;
            
            int cons = consumption_matrix[c_index];
            int exp = export_matrix[c_index];
            int net = net_matrix[c_index];
            
            if (i == 0) { 
                cons += (int)real_consumption;
                exp += (int)real_export;
                net += (int)(real_consumption - real_export); 
                
                int mins_left = 15 - (minutes_since_midnight % 15);
                hprintf255(request, "<tr style='color:#0099FF; font-weight:bold;'><td>Now (-%dmin)</td><td>%dW / %dW</td><td>%dW</td></tr>", 
                           mins_left, cons, exp, net);
            } else {
                int row_mins = interval_of_day * 15;
                int row_h = row_mins / 60;
                int row_m = row_mins % 60;
                
                hprintf255(request, "<tr><td>%02dh%02d</td><td>%dW / %dW</td><td>%dW</td></tr>", 
                           row_h, row_m, cons, exp, net);
            }
        }

        poststr(request, 
            "</tbody></table></div>"
            "<div style='flex:0 0 340px; display:flex; justify-content:center; align-items:center; background:#222; border-radius:8px; padding:10px; overflow:hidden;'>"
        );
        
        hprintf255(request, 
            "<div id='d-clk' style='font-size:110px; font-weight:bold; color:#0099FF; font-family:monospace; line-height:1; letter-spacing:-4px;'>%02d:%02d</div>"
            "</div></div>", 
            NTP_GetHour(), NTP_GetMinute()
        );

        // ====================================================================
        // 6. ASYNCHRONOUS SWAP ENGINE & STATE SYNC
        // ====================================================================
        hprintf255(request, "<div id='sys-data' data-dmp='%d' data-auto='%d' style='display:none;'></div>", dump_load_relay[5], charger_c_auto);
        
        poststr(request, "<script>");
        hprintf255(request, "var dmp=%d, auto=%d;", dump_load_relay[5], charger_c_auto);
        
        poststr(request, 
            "function upd(v){if(auto===1)return; dmp=parseInt(v);fetch('/cm?cmnd=SetDumpLoad%20'+dmp);"
            "document.getElementById('inv-btn').style.background=(dmp===5)?'#4caf50':'#555555';"
            "document.getElementById('chg-btn').style.background=(dmp>18)?'#4caf50':((dmp>=10&&dmp<=18)?'#ffeb3b':'#555555');"
            "document.getElementById('chg-30-btn').style.background=(dmp>=30)?'#4caf50':'#555555';"
            "document.getElementById('chg-80-btn').style.background=(dmp>=80)?'#4caf50':'#555555';"
            "var tc=document.getElementById('c-v'),tl=document.getElementById('c-lbl');"
            "if(tc&&tl){if(dmp===0){tl.innerText='Charger';tc.innerText='Idle';tc.style.color='#888';}"
            "else if(dmp===5){tl.innerText='Charger';tc.innerText='Battery';tc.style.color='#4caf50';}"
            "else{tl.innerText='Charging';tc.innerText=dmp+'%';tc.style.color='#0099FF';}}}"
            "function t_inv(){upd(dmp===5?0:5);}function t_chg(){upd(dmp>=10?0:18);}"
            "function tm(){auto=(auto===1)?0:1; fetch('/cm?cmnd=ToggleAuto');"
            "var b=document.getElementById('m-btn');if(auto===0){b.innerText='MANUAL';b.style.background='#f44336';}else{b.innerText='AUTO';b.style.background='#0099FF';}}"
            "function rsh(ids){fetch('/index').then(r=>r.text()).then(html=>{"
            "var doc=new DOMParser().parseFromString(html,'text/html');"
            "var sys=doc.getElementById('sys-data');if(sys){dmp=parseInt(sys.getAttribute('data-dmp'));auto=parseInt(sys.getAttribute('data-auto'));}"
            "ids.forEach(id=>{"
            "var oldEl=document.getElementById(id),newEl=doc.getElementById(id);"
            "if(oldEl&&newEl){"
            "if(oldEl.innerHTML!==newEl.innerHTML) oldEl.innerHTML=newEl.innerHTML;"
            "oldEl.className=newEl.className; oldEl.style.color=newEl.style.color; oldEl.style.background=newEl.style.background;"
            "}});}).catch(e=>console.log(e));}"
            "setInterval(function(){rsh(['d-va','d-pwr','d-est','d-bal','d-chg-box','d-sens-body','d-clk','inv-btn','chg-btn','chg-30-btn','chg-80-btn','m-btn']);}, 10000);"
            "setInterval(function(){rsh(['d-graph','d-hist-body']);}, 30000);"
            "</script>"
        );
    }
    
    poststr(request, "</div>"); 
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

// Custom handler to set Dump Load relay manually via JS
commandResult_t BL09XX_SetDumpLoad(const void *context, const char *cmd, const char *args, int cmdFlags)
{
    // The Iron-Clad Guard: Refuse manual HTTP updates if the system is in AUTO mode.
    if (charger_c_auto == 1) return CMD_RES_OK; 
    
    if(args && *args) {
        dump_load_relay[5] = atoi(args);
        
        // Push the command instantly when updated in manual mode
        char dgr_cmd[64];
        snprintf(dgr_cmd, sizeof(dgr_cmd), "DGR_SendDimmer solar_dump %d", dump_load_relay[5]);
        CMD_ExecuteCommand(dgr_cmd, 0);

        char fallback_cmd[64];
        snprintf(fallback_cmd, sizeof(fallback_cmd), "SendGet http://192.168.8.%d/cm?cmnd=Channel3%%20%d", charger_c_ip, dump_load_relay[5]);
        CMD_ExecuteCommand(fallback_cmd, 0);
    }
    return CMD_RES_OK;
}

// Toggle Auto Command Handler
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

            // Charger C reset handled in calculation
        }
        // ------------------------------------------------------------------------------------------------------

        if (!(check_time == old_time))
        {
            min_reset = 1;
            old_time = check_time;
            lastsync++;
        }
                                                         
        net_energy = (real_consumption - real_export);                               

        current_minute = check_time;
        
        // ======================================================================================================
        // THE 1-MINUTE CALCULATION LOOP (Cleaned and Simplified)
        // ======================================================================================================
        if (current_minute != last_minute) 
        {
            last_minute = current_minute;
            
            int min_in_block = current_minute % 15; 
            int check_time_estimate_mins = 15 - min_in_block; 
            
            // 1. Predict total Wh accumulated by the end of the 15-minute period
            estimated_energy_period = (int)net_energy + ((int)sensors[OBK_POWER].lastReading * check_time_estimate_mins) / 60;
            
            // 2. Extrapolate immediate equivalent energy
            if (min_in_block > 0) {
                net_energy_equivalent = (int)((float)net_energy * (15.0f / min_in_block));                                               
            } else {
                net_energy_equivalent = (int)net_energy; 
            }

            // 3. NEW SOLAR STATUS LOGIC
            if (net_energy <= -26.0f) {
                solar_available = 1;
            } else if (net_energy > 14.0f) {
                solar_available = 0;
            }

            // ====================================================================
            // ISOLATED LOGIC BLOCK (ONLY RUNS IN AUTO MODE)
            // ====================================================================
            if (charger_c_auto == 1) {

                if (solar_available == 0) {
                    if (net_energy >= 6.0f) {
                        dump_load_relay[5] = 5;
                    } else if (net_energy <= -6.0f) {
                        dump_load_relay[5] = 0;
                    }
                } 
                else {
                    if (net_energy > -10.0f) {
                        if (dump_load_relay[5] > 18) {
                            dump_load_relay[5] = 18;
                        }
                    } 
                    else if (net_energy <= -10.0f && net_energy > -20.0f) {
                        dump_load_relay[5] = 18;
                    } 
                    else if (net_energy <= -20.0f) {
                        int calculated_pwr = (abs((int)net_energy) * 60 / check_time_estimate_mins) / 10;
                        
                        if (calculated_pwr > 100) calculated_pwr = 100;
                        if (calculated_pwr < 20) calculated_pwr = 20;
                        
                        dump_load_relay[5] = calculated_pwr;
                    }
                }
            } // END OF AUTO MODE BLOCK

            // ====================================================================
            // UNCONDITIONAL SEND: Runs every 1-minute regardless of Auto/Manual
            // ====================================================================
            char dgr_cmd[64];
            snprintf(dgr_cmd, sizeof(dgr_cmd), "DGR_SendDimmer solar_dump %d", dump_load_relay[5]);
            CMD_ExecuteCommand(dgr_cmd, 0);

            char fallback_cmd[64];
            snprintf(fallback_cmd, sizeof(fallback_cmd), "SendGet http://192.168.8.%d/cm?cmnd=Channel3%%20%d", charger_c_ip, dump_load_relay[5]);
            CMD_ExecuteCommand(fallback_cmd, 0);

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

    // Register our newly created JS backend handler
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

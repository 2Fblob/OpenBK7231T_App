// Updated version without using bool, true, false keywords.

#define INTERVAL_MINUTES 15
#define INTERVALS_PER_DAY (24 * 60 / INTERVAL_MINUTES)
#define INTERVALS_PER_HOUR (60 / INTERVAL_MINUTES)

static int consumption_array[96] = {0};
static int export_array[96] = {0};
static int net_metering_mode = 0; // 0 = No net metering, 1 = 15min net, 2 = 60min net
static int last_interval = -1;
static float net_energy = 0;
static float real_export = 0;
static float real_consumption = 0;
static int save_to_flash_flag = 0;

void BL09XX_AppendInformationToHTTPIndexPage(http_request_t *request) {
    if (CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE)) {
        int total_consumption = 0;
        int total_export = 0;

        if (NTP_IsTimeSynced()) {
            int minutes_since_midnight = NTP_GetHour() * 60 + NTP_GetMinute();
            int current_interval = (net_metering_mode == 2) ? NTP_GetHour() : (minutes_since_midnight / 15);

            int total_rows = (net_metering_mode == 2) ? 24 : 96;

            for (int q = 0; q < total_rows; q++) {
                int hour = (net_metering_mode == 2) ? q : (q / 4);
                int minute = (net_metering_mode == 2) ? 0 : (q % 4) * 15;

                int consumption = consumption_array[q];
                int exportv = export_array[q];
                int net = consumption - exportv;

                if (q == current_interval) {
                    hprintf255(request, "<tr><td><b>%i:%02i</b></td>", hour, minute);
                    hprintf255(request, "<td><b>%dW</b></td>", consumption);
                    hprintf255(request, "<td><b>%dW</b></td>", exportv);
                    hprintf255(request, "<td><b>%dW</b></td></tr>", net);
                } else {
                    hprintf255(request, "<tr><td>%i:%02i</td>", hour, minute);
                    hprintf255(request, "<td>%dW</td>", consumption);
                    hprintf255(request, "<td>%dW</td>", exportv);
                    hprintf255(request, "<td>%dW</td></tr>", net);
                }

                total_consumption += (net > 0) ? net : 0;
                total_export += (net < 0) ? -net : 0;
            }

            poststr(request, "<h4>Totals:</h4>");
            hprintf255(request, "<font size=2>- Net Consumption: <b>%iW</b>, Net Export: <b>%iW</b><br></font>", total_consumption, total_export);
        }
    }
}

void BL_ProcessUpdate(...) {
    if (NTP_IsTimeSynced()) {
        int minutes_since_midnight = NTP_GetHour() * 60 + NTP_GetMinute();
        int current_interval = (net_metering_mode == 2) ? NTP_GetHour() : (minutes_since_midnight / 15);

        if (net_metering_mode == 0) {
            sensors[OBK_CONSUMPTION_TOTAL].lastReading += real_consumption;
            sensors[OBK_GENERATION_TOTAL].lastReading += real_export;
        } else {
            if (current_interval != last_interval) {
                if (last_interval >= 0) {
                    float net = consumption_array[last_interval] - export_array[last_interval];

                    if (net > 0) {
                        sensors[OBK_CONSUMPTION_TOTAL].lastReading += net;
                    } else {
                        sensors[OBK_GENERATION_TOTAL].lastReading += fabsf(net);
                    }
                }
                last_interval = current_interval;
            }

            consumption_array[current_interval] += real_consumption;
            export_array[current_interval] += real_export;

            // Handle day rollover
            int reset_needed = 0;
            if ((net_metering_mode == 1) && (current_interval == 0) && (last_interval == 95)) {
                reset_needed = 1;
            }
            if ((net_metering_mode == 2) && (current_interval == 0) && (last_interval == 23)) {
                reset_needed = 1;
            }

            if (reset_needed != 0) {
                float net = consumption_array[last_interval] - export_array[last_interval];
                if (net > 0) {
                    sensors[OBK_CONSUMPTION_TOTAL].lastReading += net;
                } else {
                    sensors[OBK_GENERATION_TOTAL].lastReading += fabsf(net);
                }

                for (int i = 0; i < 96; i++) {
                    consumption_array[i] = 0;
                    export_array[i] = 0;
                }
                last_interval = -1;
            }
        }

        if ((NTP_GetMinute() == 0) && (save_to_flash_flag == 0)) {
            save_to_flash_flag = 1;
        }

        if (save_to_flash_flag != 0) {
            save_to_flash_flag = 0;
            // Your Flash saving code here
        }
    }
}

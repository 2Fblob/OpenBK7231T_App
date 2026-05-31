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

    // Start Master Two-Column Table
    poststr(request, "<hr><table style='width:100%; vertical-align: top;'><tr><td style='width:50%; vertical-align: top;'>");
    
    // Left Column: Sensor Table
    poststr(request, "<table style='width:100%'>");

	for (int i = (OBK__FIRST); i <= (OBK_CONSUMPTION__DAILY_LAST); i++) {
		if (i == OBK_GENERATION_TOTAL && (!CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE))){i++;}
		if (i <= OBK__NUM_MEASUREMENTS || NTP_IsTimeSynced()) {
			poststr(request, "<tr><td><b>");
			poststr(request, sensors[i].names.name_friendly);
			poststr(request, "</b></td><td style='text-align: right;'>");
			if ((i == OBK_CONSUMPTION_TOTAL) || (i == OBK_GENERATION_TOTAL))
			{
				hprintf255(request, "%.*f</td><td>kWh</td>", sensors[i].rounding_decimals, (0.001*sensors[i].lastReading));
			}
			else
			{
				hprintf255(request, "%.*f</td><td>%s</td>", sensors[i].rounding_decimals, sensors[i].lastReading, sensors[i].names.units);
			}
		}
	};
	
	poststr(request, "</table>");
	hprintf255(request, "<font size=1>Saving Interval: %.2fW</font>", changeSavedThresholdEnergy);

    // Switch to Right Column: System Status
    poststr(request, "</td><td style='width:50%; vertical-align: top; padding-left: 20px;'>");

    if (energyCounterStatsEnable == true)
	{	
		poststr(request,"<h4>Current system status:</h4>");
		hprintf255(request,"<font size=2>- Storage Inverter: <b>%i</b>, Total time: <b>%i</b> <br></font>", dump_load_relay[0], dump_load_relay_timer[0]); 
		hprintf255(request,"<font size=2>- Storage Charger A: <b>%i</b>, Total time: <b>%i</b> <br></font>", dump_load_relay[1], dump_load_relay_timer[1]); 
		hprintf255(request,"<font size=2>- Storage Charger B: <b>%i</b>, Total time: <b>%i</b> <br></font>", dump_load_relay[3], dump_load_relay_timer[2]); 
		hprintf255(request,"<font size=2>- Washer/Dishwasher: <b>%i</b>, Total time: <b>%i</b> <br></font>", dump_load_relay[2], dump_load_relay_timer[3]); 
		hprintf255(request,"<font size=2>- Basement Dehumidifier: <b>%i</b>, Total time: <b>%i</b> <br></font>", dump_load_relay[4], dump_load_relay_timer[4]); 

		hprintf255(request,"<font size=2>- Solar available: <b>%i</b><br></font>", solar_available); 
		
		if (net_energy_equivalent < 0)
		{
		    hprintf255(request,"<font size=2>- Net energy equivalent: <b>%i</b><br></font>", net_energy_equivalent); 
		}

        hprintf255(request,"<font size=2>- 15-Min Estimation: <b>%i Wh</b><br></font>", estimated_energy_period);
        hprintf255(request,"<font size=2 color=#0099FF>- Charger C PWM: <b>%i%%</b><br><br></font>", dump_load_relay[5]);
	
        int minutes_since_last_interval = minutes_since_midnight % net_metering_period;
        int minutes_till_next_interval = 15-minutes_since_last_interval;
		
        // Cleaned up NetMetering stats
        hprintf255(request,"<b>NetMetering (Last %d min out of %d): %.3f Wh</b><br><br>", minutes_since_last_interval , net_metering_period, net_energy); 
        hprintf255(request,"<b>%d min to next cycle</b>", minutes_till_next_interval); 
    }

    // Close Master Table
    poststr(request, "</td></tr></table>");

    // Full-Width Bottom Section: Matrix Table
	if (CFG_HasFlag(OBK_FLAG_POWER_ALLOW_NEGATIVE))
	{
        poststr(request, "<br><h2>Energy Stats (Last 6 Hours)</h2>");
        poststr(request, "<table style='width:100%; text-align: center;'>");
        poststr(request, "<tr><th style='text-align: left;'>Time </th><th>Import </th><th>Export </th><th>Net </th></tr><hr>");

        if (NTP_IsTimeSynced()) {
            minutes_since_midnight = NTP_GetHour() * 60 + NTP_GetMinute();
            int current_interval_of_day = minutes_since_midnight / net_metering_period;

            // Loop 24 intervals (6 hours). i=0 is current live interval.
            for (int i = 0; i < 24; i++) { 
                
                int interval_of_day = current_interval_of_day - i;
                
                // Wrap around to yesterday's intervals seamlessly
                if (interval_of_day < 0) { interval_of_day += 96; } 
                
                // Maps the interval of the day to our 24-slot circular buffer
                int buffer_index = interval_of_day % 24;

                const char* start_tag = (i == 0) ? "<b>" : "";
                const char* end_tag = (i == 0) ? "</b>" : "";
                
                int hour = interval_of_day / 4;
                int minute = (interval_of_day % 4) * 15;
                
                if (i == 0) {
                    // Active Row: Show full data
                    int disp_cons = consumption_matrix[buffer_index] + (int)real_consumption;
                    int disp_exp = export_matrix[buffer_index] + (int)real_export;
                    int disp_net = net_matrix[buffer_index] + (int)(real_consumption - real_export);
                    
                    hprintf255(request, "<tr><td style='text-align: left;'> %s%02i:%02i%s </td><td> %s%dW%s </td><td> %s%dW%s </td><td> %s%dW%s </td></tr>", 
                               start_tag, hour, minute, end_tag, start_tag, disp_cons, end_tag, start_tag, disp_exp, end_tag, start_tag, disp_net, end_tag);
                } else {
                    // History Rows: Show time and net only
                    int disp_net = net_matrix[buffer_index];
                    hprintf255(request, "<tr><td style='text-align: left;'> %02i:%02i </td><td> - </td><td> - </td><td> %dW </td></tr>", 
                               hour, minute, disp_net);
                }
            }
        }
        poststr(request, "</table>");
	}
}

// Apply sign convention
    float signedPower = CFG_HasFlag(OBK_FLAG_POWER_INVERT_AC) ? (-1.0f * power) : power;

    // ====================================================================
    // 10-SECOND TICK LOGIC (INSTANTANEOUS SENSORS + ACCUMULATED ENERGY)
    // ====================================================================
    #define SAMPLES_PER_UPDATE 10

    static int   sampleCount = 0;
    static float energyAccum = 0.0f;

    // Energy must always be summed so consumption data is not lost between updates
    energyAccum += energyWh;
    sampleCount++;

    if (sampleCount < SAMPLES_PER_UPDATE) {
        return; // Do nothing else until the 10th call
    }

    // On the 10th call, pass instantaneous readings from THIS exact sample,
    // alongside the total energy accumulated over the last 10 samples.
    float totalEnergyWh = energyAccum;

    BL_ProcessUpdate(voltage, current, signedPower, frequency, totalEnergyWh);

    // Reset counters for the next 10-second window
    energyAccum = 0.0f;
    sampleCount = 0;
}


/*  Energy monitor and solar power diverter for solar PV system
    based on emonTx hardware from OpenEnergyMonitor http://openenergymonitor.org/emon/
    this version implements a phase-locked loop to synchronise to the 50Hz supply.

    Based on Martin Roberts' work (02/12/12)

    History: /
*/

#define DEBUG_HARD

//--------------------------------------------------------------------------------------------------
// Arduino I/O pin useage
#define VOLTSPIN 0
#define CT1PIN 1
#define CT2PIN 2
#define LEDPIN 9
#define SYNCPIN 6 // this output will be a 50Hz square wave locked to the 50Hz input
#define TRIACPIN 3 // triac driver pin
//--------------------------------------------------------------------------------------------------

#include <Arduino.h>
#include <util/crc16.h>

//--------------------------------------------------------------------------------------------------
// constants which must be set for each system
const float VCAL = 217;  // calculated value is 230:9 for transformer x 11:1 for resistor divider = 281
// with oscillo 230:1.06 (Vrms from resistor divider)

const float I1CAL = 60.0; // calculated value is 60A, gives 1V
const float I2CAL = 60.0; // this is for CT2, the solar PV current transformer
const int I1LEAD = 5; // number of microseconds the CT1 input leads the voltage input by
const int I2LEAD = 5; // number of microseconds the CT2 input leads the voltage input by
const int POWERCORRECTION = 0; // this value, in watts, may be used to compensate for the leakage from
                   //  voltage to current inputs, it only affects data sent to emonGLCD
const int LOAD_POWER = 2770; // power in watts (at 240V) of triac load for diverted power calculation
//#define LEDISLOCK // comment this out for LED pulsed during transmission
//--------------------------------------------------------------------------------------------------

//--------------------------------------------------------------------------------------------------
// other system constants
const float SUPPLY_VOLTS = 4.8;
const int SUPPLY_FREQUENCY = 50;
const int NUMSAMPLES = 50;// number of times to sample each 50Hz cycle
const int ENERGY_BUFFER_SIZE = 3600; // 0.001 kWh = 3600 Joules
const int BUFFER_HIGH_THRESHOLD = 2700; // energy buffer level to start diversion
const int BUFFER_LOW_THRESHOLD = 900; // energy buffer level to stop diversion
const int FILTERSHIFT =13; // for low pass filters to determine ADC offsets
const int PLLTIMERRANGE =100; // PLL timer range limit ~+/-0.5Hz
const int PLLLOCKRANGE  = 40; // allowable ADC range to enter locked state
const int PLLUNLOCKRANGE = 80; // allowable ADC range to remain locked
const int PLLLOCKCOUNT = 100; // number of cycles to determine if PLL is locked
const int LOOPTIME = 5000; // time of outer loop in milliseconds, also time between radio transmissions
//--------------------------------------------------------------------------------------------------

//--------------------------------------------------------------------------------------------------
// constants calculated at compile time
const float V_RATIO = (VCAL * SUPPLY_VOLTS)/1024;
const float I1_RATIO = (I1CAL * SUPPLY_VOLTS)/1024;
const float I2_RATIO = (I2CAL * SUPPLY_VOLTS)/1024;
const float I1PHASESHIFT = (I1LEAD+63)*256/400; // phase shift in voltage to align to current samples
const float I2PHASESHIFT = (I2LEAD+127)*256/400; //  these are fractions (x256) of sample period
const float JOULES_PER_BUFFER_UNIT = V_RATIO * I1_RATIO/SUPPLY_FREQUENCY*NUMSAMPLES;
const float MAXAVAILABLEENERGY = ENERGY_BUFFER_SIZE/JOULES_PER_BUFFER_UNIT;
const float HIGHENERGYLEVEL = BUFFER_HIGH_THRESHOLD/JOULES_PER_BUFFER_UNIT;
const float LOWENERGYLEVEL = BUFFER_LOW_THRESHOLD/JOULES_PER_BUFFER_UNIT;
const long FILTERROUNDING = (1<<(FILTERSHIFT-1));
const int TIMERTOP = (20000/NUMSAMPLES*16)-1; // terminal count for PLL timer
const int PLLTIMERMAX = TIMERTOP+PLLTIMERRANGE;
const int PLLTIMERMIN = TIMERTOP-PLLTIMERRANGE;
//--------------------------------------------------------------------------------------------------

int sampleV,sampleI1,sampleI2,numSamples;
int voltsOffset=512,I1Offset=512,I2Offset=512; // start offsets at ADC centre
float Vrms,I1rms,I2rms;
long sumVsquared,sumI1squared,sumI2squared,sumP1,sumP2;
long cycleVsquared,cycleI1squared,cycleI2squared,cycleP1,cycleP2;
long totalVsquared,totalI1squared,totalI2squared,totalP1,totalP2;
long sumTimerCount;
float realPower1,apparentPower1,powerFactor1;
float realPower2,apparentPower2,powerFactor2;
float divertedPower;
float frequency;
word timerCount=TIMERTOP;
word pllUnlocked=PLLLOCKCOUNT;
word cycleCount;
boolean newCycle,divertedCycle;
int divertedCycleCount;
unsigned long nextTransmitTime;
long availableEnergy;
int manualPowerLevel;

void setup()
{
  pinMode(LEDPIN, OUTPUT);
  digitalWrite(LEDPIN, HIGH);
  pinMode(SYNCPIN, OUTPUT);
  digitalWrite(SYNCPIN, LOW);
  pinMode(TRIACPIN,OUTPUT);
  digitalWrite(TRIACPIN,LOW);
  manualPowerLevel=0;

  nextTransmitTime=millis();
  Serial.begin(9600);
  // change ADC prescaler to /64 = 250kHz clock
  // slightly out of spec of 200kHz but should be OK
  ADCSRA &= 0xf8;  // remove bits set by Arduino library
  ADCSRA |= 0x06;

  //set timer 1 interrupt for required period
  noInterrupts();
  TCCR1A = 0; // clear control registers
  TCCR1B = 0;
  TCNT1  = 0; // clear counter
  OCR1A = TIMERTOP; // set compare reg for timer period
  bitSet(TCCR1B,WGM12); // CTC mode
  bitSet(TCCR1B,CS10); // no prescaling
  bitSet(TIMSK1,OCIE1A); // enable timer 1 compare interrupt
  bitSet(ADCSRA,ADIE); // enable ADC interrupt
  interrupts();
}

void updatePLL(int newV, int lastV)
{
  static byte samples=0;
  static int oldV;
  static boolean divertFlag, diverting=false;
  static int manualCycleCount=-1;
  boolean rising;

  rising=(newV>lastV); // synchronise to rising zero crossing

  samples++;
  if(samples>=NUMSAMPLES) // end of one 50Hz cycle
  {
    digitalWrite(SYNCPIN,HIGH);
    samples=0;
    if(rising)
    {
      // if we're in the rising part of the 50Hz cycle adjust the final timer count
      // to move newV towards 0, only adjust if we're moving in the wrong direction
      if(((newV<0)&&(newV<=oldV))||((newV>0)&&(newV>=oldV))) timerCount-=newV;
      // limit range of PLL frequency
      timerCount=constrain(timerCount,PLLTIMERMIN,PLLTIMERMAX);
      OCR1A=timerCount;
      if(abs(newV)>PLLUNLOCKRANGE) pllUnlocked=PLLLOCKCOUNT; // we're unlocked
      else if(pllUnlocked) pllUnlocked--;
#ifdef LEDISLOCK
      digitalWrite(LEDPIN,pllUnlocked?LOW:HIGH);
#endif
    }
    else // in the falling part of the cycle, we shouldn't be here
    {
      OCR1A=PLLTIMERMAX; // shift out of this region fast
      pllUnlocked=PLLLOCKCOUNT; // and we can't be locked
    }

    oldV=newV;

    // save results for outer loop
    cycleVsquared=sumVsquared;
    cycleI1squared=sumI1squared;
    cycleI2squared=sumI2squared;
    cycleP1=sumP1;
    cycleP2=sumP2;
    divertedCycle=divertFlag;
    // and clear accumulators
    sumVsquared=0;
    sumI1squared=0;
    sumI2squared=0;
    sumP1=0;
    sumP2=0;
    divertFlag=false;
    newCycle=true; // flag new cycle to outer loop
    if(manualPowerLevel) manualCycleCount++;
    else manualCycleCount=-1; // manual power is off
  }
  else if(samples==(NUMSAMPLES/2))
  {
    // negative zero crossing
    digitalWrite(SYNCPIN,LOW);
  }
  else if(samples==((NUMSAMPLES/2)-4)) // fire triac ~1.6ms before -ve zero crossing
  {
    if(availableEnergy > HIGHENERGYLEVEL) diverting=true;
    else if(availableEnergy < LOWENERGYLEVEL) diverting=false;

    if(diverting || (manualCycleCount>=manualPowerLevel))
    {
      digitalWrite(TRIACPIN,HIGH);
      divertFlag=true;
      manualCycleCount=0;
    }
    else digitalWrite(TRIACPIN,LOW);
  }
}


// timer 1 interrupt handler
ISR(TIMER1_COMPA_vect)
{
  ADMUX = _BV(REFS0) | VOLTSPIN; // start ADC conversion for voltage
  ADCSRA |= _BV(ADSC);
}

// ADC interrupt handler
ISR(ADC_vect)
{
  static int newV,newI1,newI2;
  static int lastV;
  static long fVoltsOffset=512L<<FILTERSHIFT,fI1Offset=512L<<FILTERSHIFT,fI2Offset=512L<<FILTERSHIFT;
  int result;
  long phaseShiftedV;

  result = ADCL;
  result |= ADCH<<8;

  // determine which conversion just completed
  switch(ADMUX & 0x0f)
  {
    case VOLTSPIN:
      ADMUX = _BV(REFS0) | CT1PIN; // start CT1 conversion
      ADCSRA |= _BV(ADSC);
      lastV=newV;
      sampleV = result;
      newV=sampleV-voltsOffset;
      sumVsquared+=((long)newV*newV);
      // update low-pass filter for DC offset
      fVoltsOffset += (sampleV-voltsOffset);
      voltsOffset=(int)((fVoltsOffset+FILTERROUNDING)>>FILTERSHIFT);
      // determine voltage at current sampling points and use it for power calculation
      phaseShiftedV=lastV+((long)((newV-lastV)*I1PHASESHIFT)>>8);
      sumP1+=(phaseShiftedV*newI1);
      phaseShiftedV=lastV+((long)((newV-lastV)*I2PHASESHIFT)>>8);
      sumP2+=(phaseShiftedV*newI2);
      break;
    case CT1PIN:
      ADMUX = _BV(REFS0) | CT2PIN; // start CT2 conversion
      ADCSRA |= _BV(ADSC);
      sampleI1 = result;
      newI1=sampleI1-I1Offset;
      sumI1squared+=((long)newI1*newI1);
      fI1Offset += (sampleI1-I1Offset);
      I1Offset=(int)((fI1Offset+FILTERROUNDING)>>FILTERSHIFT);
      break;
    case CT2PIN:
      sampleI2 = result;
      newI2=sampleI2-I2Offset;
      sumI2squared+=((long)newI2*newI2);
      fI2Offset += (sampleI2-I2Offset);
      I2Offset=(int)((fI2Offset+FILTERROUNDING)>>FILTERSHIFT);
      updatePLL(newV,lastV);
      break;
  }
}

// add data for new 50Hz cycle to total
void addCycle()
{
  totalVsquared+=cycleVsquared;
  totalI1squared+=cycleI1squared;
  totalI2squared+=cycleI2squared;
  totalP1+=cycleP1;
  totalP2+=cycleP2;
  numSamples+=NUMSAMPLES;
  sumTimerCount+=(timerCount+1); // for average frequency calculation
  availableEnergy-=cycleP1; // Solar energy is negative at this point
  availableEnergy=constrain(availableEnergy,0,MAXAVAILABLEENERGY);
  if(divertedCycle) divertedCycleCount++;
  cycleCount++;
  newCycle=false;
}

// calculate voltage, current, power and frequency
void calculateVIPF()
{
  if(numSamples==0) return; // just in case

  Vrms = V_RATIO * sqrt(((float)totalVsquared)/numSamples);
  I1rms = I1_RATIO * sqrt(((float)totalI1squared)/numSamples);
  I2rms = I2_RATIO * sqrt(((float)totalI2squared)/numSamples);

  realPower1 = (V_RATIO * I1_RATIO * (float)totalP1)/numSamples;
  if(abs(realPower1)>POWERCORRECTION) realPower1-=POWERCORRECTION;
  apparentPower1 = Vrms * I1rms;
  powerFactor1=abs(realPower1 / apparentPower1);
  realPower2 = (V_RATIO * I2_RATIO * (float)totalP2)/numSamples;
  if(abs(realPower2)>POWERCORRECTION) realPower2-=POWERCORRECTION;
  apparentPower2 = Vrms * I2rms;
  powerFactor2=abs(realPower2 / apparentPower2);
  divertedPower=((float)divertedCycleCount*LOAD_POWER)/cycleCount;
  divertedPower=divertedPower*(Vrms/240)*(Vrms/240); // correct power for actual voltage
  // TODO: correct 240??
  frequency=((float)cycleCount*16000000)/(((float)sumTimerCount)*NUMSAMPLES);

  totalVsquared=0;
  totalI1squared=0;
  totalI2squared=0;
  totalP1=0;
  totalP2=0;
  numSamples=0;
  cycleCount=0;
  divertedCycleCount=0;
  sumTimerCount=0;
}

void sendResults()
{
  #ifdef DEBUG_HARD
    Serial.print(voltsOffset);
    Serial.print(" ");
    Serial.print(I1Offset);
    Serial.print(" ");
    Serial.print(I2Offset);
    Serial.print(" ");
  #endif
  Serial.print(Vrms);
  Serial.print(" ");
  Serial.print(I1rms);
  Serial.print(" ");
  Serial.print(I2rms);
  Serial.print(" ");
  Serial.print(realPower1);
  Serial.print(" ");
  Serial.print(realPower2);
  Serial.print(" ");
  Serial.print(divertedPower);
  Serial.print(" ");
  Serial.print(frequency);
  Serial.print(" ");
  Serial.print(" ");
  Serial.print((float)availableEnergy * JOULES_PER_BUFFER_UNIT);
  if(pllUnlocked) Serial.print(" PLL is unlocked ");
  else Serial.print(" PLL is locked ");
  Serial.println();
}

void loop()
{
  if(newCycle) addCycle(); // a new mains cycle has been sampled

  if((millis()>=nextTransmitTime) && ((millis()-nextTransmitTime)<0x80000000L)) // check for overflow
  {
#ifndef LEDISLOCK
    digitalWrite(LEDPIN,HIGH);
#endif
    calculateVIPF();
    sendResults();
    nextTransmitTime+=LOOPTIME;
#ifndef LEDISLOCK
    digitalWrite(LEDPIN,LOW);
#endif
  }

  if(Serial.available())
  {
    manualPowerLevel=Serial.parseInt();
    manualPowerLevel=constrain(manualPowerLevel,0,255);
    Serial.print("manual power level set to ");
    Serial.println(manualPowerLevel);
  }
}

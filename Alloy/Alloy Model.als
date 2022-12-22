//-------------------------------------------------------------------------------------//
//------------------------------------Signatures------------------------------------//
//-------------------------------------------------------------------------------------//

//------------------------------------USERS----------------------------------------//
abstract sig User {
}

sig EndUser extends User {
	paymentMethod: one PaymentMethod,
	calendar: lone Calendar,
	vehicles: set Vehicle, 
	bookings: set Booking, 
	charges: set Charge 
}

sig CPO extends User {
	chargingStations: set ChargingStation
}

//-------------------------------------eMSS-----------------------------------------//
abstract sig Notification {
	enduser: one EndUser,
	dateTime: one DateTime,
	description: one String
}

sig Reminder extends Notification {
	booking: one Booking
}

sig ChargingEnd extends Notification {
	charge: one Charge
}

sig Suggestion extends Notification {
	chargingStation: some ChargingStation
}

sig Vehicle {
}

sig Booking {
	start: one DateTime,
	end: one DateTime,
	chargingSocket: one ChargingSocket
}

sig PaymentMethod {

}

sig Payment {
	isPayed: one Boolean,
	paymentMethod: one PaymentMethod
}

//-------------------------------------CPMS-----------------------------------------//
sig ChargingStation {
	location: one Location,
	cost: one CostTable,
	chargingSockets: some ChargingSocket,
	listDSO: some DSO //maybe we could remove this and let it be only in the CPO
}

sig ChargingSocket {
	isOccupied: one Boolean,
	//powerSupplied: one Int,
	type: one ChargingSocketType
}//{powerSupplied>0}

sig SpecialOffer {
	startTime: one DateTime,
	endTime: one DateTime,
	prices: one CostTable
}

//-------------------------------------shared classes------------------------------//
sig Charge {
	enduser: one EndUser,
	startTime: one DateTime,
	endTime: one DateTime,
	cost: one Float,
	timeToFinish: one DateTime,
	payment: one Payment,
	chargingSocket: one ChargingSocket
}

//-------------------------------------external classes---------------------------//
sig Calendar{}

sig DSO{}

//------------------------------------- Defining new types------------------------------------//
abstract sig ChargingSocketType {}
one sig SLOW extends ChargingSocketType{}
one sig FAST extends ChargingSocketType{}
one sig RAPID extends ChargingSocketType{}

abstract sig Boolean {}
one sig TRUE extends Boolean{}
one sig FALSE extends Boolean{}

sig DateTime{}

sig Location {}

sig CostTable{}

sig Float {}

//-------------------------------------------------------------------------------------//
//------------------------------------Facts------------------------------------------//
//-------------------------------------------------------------------------------------//

fact eachEndUserHasOnePaymentMethod {
	all e: EndUser | one p: PaymentMethod |
		e.paymentMethod = p
}

fact eachPaymentMethodIsOwnedByOneEndUser {
	all p: PaymentMethod | one e: EndUser |
		e.paymentMethod = p 
}

fact eachVehicleOwnedByOneEndUser {
	all v: Vehicle | one e: EndUser |
		v in e.vehicles
}

fact eachBookingOwnedByOneEndUser {
	all b: Booking | one e: EndUser |
		b in e.bookings
}

fact eachNotificationOwnedByOneEndUser {
	all n: Notification | one e: EndUser |
		n.enduser = e 
}
	
fact eachReminderAssociatedToOneBooking {
	all r: Reminder | one b: Booking |
		r.booking = b
}

fact eachBookingAssociatedToOneReminder {
	all b: Booking | one r: Reminder |
		r.booking = b
}

fact eachChargeAssociatedToOneEndUser {
	all c: Charge | one e: EndUser |
		c in e.charges and c.enduser = e
}

fact eachPaymentAssociatedToOneCharge {
	all p: Payment | one c: Charge |
		c.payment = p
}

fact eachChargeAssociatedToOnePayment {
	all c: Charge | one p: Payment |
		c.payment = p
}

fact eachPaymentAssociatedToOnePaymentMethod {
	all p: Payment | one pm: PaymentMethod |
		p.paymentMethod = pm
}

fact oneUserForCalendar {
	all c: Calendar | one e: EndUser |
		e.calendar = c
}

// Distinct constraints

fact everyPaymentMethodIsDifferent {
	all e1, e2: EndUser | 
		e1 != e2 implies e1.paymentMethod != e2.paymentMethod
}
	

//------------ CPMS constraints -------------
fact eachStationIsOwnedByOneCPO {
	all s: ChargingStation | one c: CPO |
		s in c.chargingStations
}

fact eachStationHasDifferentLocation {
	all l : Location | one c : ChargingStation | 
		c.location = l
}

fact eachSocketInOneStation {
	all so: ChargingSocket | one st: ChargingStation |
		so in st.chargingSockets
}

fact eachSocketHasType {
	all s: ChargingSocket | one t: ChargingSocketType|
		s.type = t
}

//---- Datetime restrictions -------

fact noDateTimeShare{
	all sp: SpecialOffer |
		sp.startTime != sp.endTime
}

//---------- Redundant instances ------------------
fact noRedundantLocations {
	all l: Location | one c: ChargingStation |
		c.location = l
}

fact noRedundantDateTime{

}

fact noRedundantCostTableChargingStations{
	all cs1, cs2: ChargingStation |
		(cs1 != cs2 implies
		cs1.cost != cs2.cost) 
}

fact noRedundantCostTableSpecialOffer{
	all sp1, sp2: SpecialOffer |
		(sp1 != sp2 implies
		sp1.prices != sp2.prices)
}

fact noRedundantCostTableBetween{
	all sp: SpecialOffer | all cs: ChargingStation |
		sp.prices != cs.cost
}

fact noRedundantInteger{}

fact noRedundantFloat{}

//-------------------------------------------------------------------------------------//
//------------------------------------Assertions-----------------------------------//
//-------------------------------------------------------------------------------------//

//in slides is said that assertions are to verify something we want to rove
//empty space because i have no idea on what we need to verify

// Marcos: I dont think we need to pt any assertions at all, fra

//-------------------------------------------------------------------------------------//
//------------------------------------Show------------------------------------------//
//-------------------------------------------------------------------------------------//

pred show {
	#CPO = 6
	#ChargingStation = 5	//something wrong in declaring this
					//maybe some fact is preventing having more stations than CPO
	#EndUser = 3
	#DSO = 1
}

run show for 10

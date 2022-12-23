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
sig Vehicle {
}

abstract sig Notification {
	dateTime: one DateTime,
}

sig Reminder extends Notification {
}


sig ChargingEnd extends Notification {
}

/*
sig Suggestion extends Notification {
	chargingStation: some ChargingStation
}
*/

sig Booking {
	start: one DateTime,
	end: one DateTime,
	chargingSocket: one ChargingSocket,
	reminder: one Reminder
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
	listDSO: some DSO, 
	listSpecialOffers: some SpecialOffer
}

sig ChargingSocket {
	isOccupied: one Boolean,
	type: one ChargingSocketType
}

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
	chargingSocket: one ChargingSocket,
	chargingNotification: one ChargingEnd 
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

sig DateTime{
	
}

sig Location {}

sig CostTable{}

sig Float {}

//-------------------------------------------------------------------------------------//
//------------------------------------Facts------------------------------------------//
//-------------------------------------------------------------------------------------//

// User facts
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

fact eachReminderHasDateTime{
	all r: Reminder | one dt: DateTime |
		r.dateTime = dt
}

fact noSharingReminders{
	all b1, b2: Booking |
		b1 != b2 implies
		b1.reminder != b2.reminder
}

fact eachBookingOwnedByOneEndUser {
	all b: Booking | one e: EndUser |
		b in e.bookings
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

fact oneChargeToOneChargingEnd{
	all c: Charge | one ch: ChargingEnd|
		c.chargingNotification = ch
}

fact noSharingChargingEng {
	all ch1, ch2: Charge |
		ch1 != ch2 implies
		(ch1.chargingNotification != ch2.chargingNotification)
}

//---------- Distinctions constraints --------- //
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

fact eachSpecialOfferBelongsToOneChargingStation{
	all spo: SpecialOffer | one ch: ChargingStation |
		spo in ch.listSpecialOffers
}

fact noSharingSpecialOffers {
	all ch1, ch2: ChargingStation |
		ch1 != ch2 implies
		((ch1.listSpecialOffers) not in ch2.listSpecialOffers)
}

//---------- Redundant instances ------------------
fact noRedundantLocations {
	all l: Location | one c: ChargingStation |
		c.location = l
}

fact noRedundantDateTimeSpecialOfffer{
	all sp: SpecialOffer |
		sp.startTime != sp.endTime
}

fact noSharingDateTimeSpecialOfffer{
	all sp1, sp2: SpecialOffer |
		sp1 != sp2 implies
		(sp1.startTime != sp2.endTime and
		sp1.startTime != sp2.startTime)
}

fact noRedundantDateTimeCharge{
	all c: Charge |
		c.startTime != c.endTime
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

fact noRedundantFloat{
	all ch1, ch2: Charge |
		ch1 != ch2 implies ch1.cost != ch2.cost
}

//No left overs

//-------------------------------------------------------------------------------------//
//------------------------------------Assertions-----------------------------------//
//-------------------------------------------------------------------------------------//

//in slides is said that assertions are to verify something we want to rove
//empty space because i have no idea on what we need to verify

// Marcos: I dont think we need to put any assertions at all, fra, just test the general structure

//-------------------------------------------------------------------------------------//
//------------------------------------Show------------------------------------------//
//------------------------------------------------------------------------------------//

pred show {
	#CPO = 2
	#ChargingStation = 3
	#EndUser = 3
	#DSO = 2
	#ChargingSocket = 4
	#Booking = 2
	#Reminder = 2
	--#Charge = 2
	#ChargingEnd = 2
}

run show for 10

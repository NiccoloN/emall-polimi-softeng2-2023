//-------------------------------------------------------------------------------------//
//------------------------------------Signatures------------------------------------//
//-------------------------------------------------------------------------------------//

//------------------------------------USERS----------------------------------------//
abstract sig User {
	id: one Int
}{id > 0}

sig EndUser extends User {
	paymentMethod: one PaymentMethod,
	calendar: lone Calendar,
	vehicles: some Vehicle, //some is not correct
	bookings: some Booking,//same
	charges: some Charge//same
}{id > 0}

sig CPO extends User {
	listDSO: some DSO,
	chargingStations: some ChargingStation
}{id > 0}

//-------------------------------------eMSS-----------------------------------------//
abstract sig Notification {
	enduser: one EndUser,
	date: one Date,
	time: one Time,
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
	id: one Int
}{id > 0}

sig Booking {
	date: one Date,
	startTime: one Time,
	endTime: one Time,
	chargingSocket: one ChargingSocket
}

sig PaymentMethod {
	//don't know what to insert
}

sig Payment {
	isPayed: one //boolean,
	paymentMethod: one PaymentMethod
}

//-------------------------------------CPMS-----------------------------------------//
sig ChargingStation {
	id: one Int,
	location: one Location,
	costs: //how do we implement these? bridge class?
	chargingSockets: some ChargingSocket,
	listDSO: some DSO
}

sig ChargingSocket {
	id: one Int,
	isOccupied: one //boolean,
	powerSupplied: one Int,
	type: one ChargingSocketType
}

enum ChargingSocketType {
	SLOW,
	FAST,
	RAPID
}

sig SpecialOffer {
	startTime: one DateTime,
	endTime: one DateTime,
	prices: //same problem as above
}

//-------------------------------------shared classes------------------------------//
sig Charge {
	enduser: one EndUser,
	startTime: one Time,
	duration: one Duration, //a lot of type to declare
	cost: one Float,
	timeToFinish: one Duration, // the same as duration?
	payment: one Payment,
	chargingSocket: one ChargingSocket
}


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

fact eachStationHasDifferentLocation {
	all l : Location | one c : ChargingStation | c.location = l
}

fact eachUserHasUniqueId {
	no disj u1 , u2 : User | u1 . id = u2 . id
}

fact eachVehicleOwnedByOneEndUser {
	all v: Vehicle | one e: EndUser |
		v in e.vehicle
}

fact eachVehicleHasUniqueId {
	no disj v1 , v2 : Vehicle | v1 . id = v2 . id
}

fact eachBookingOwnedByOneEndUser {
	all b: Booking | one e: EndUser |
		b in e.bookings
}

fact eachNotificationOwnedByOneEndUser {
	all n: Notification | one e: EndUser |
		n.enduser = e 
} // not sure if we can specify it for the abstract class to let the sub inherit

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

//all "distinct" constraints...
//all CPMS constraints...












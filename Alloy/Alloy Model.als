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
	vehicles: some Vehicle, //For the vehicle it seems correct, need at neast one vehicle BUT the vehicle must already exist, isn't it?
	bookings: set Booking, //Maybe set because the user may not book nothing, just create an account
	charges: set Charge //same
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
	//Payment method may vary... I don't remember if we assumed PayPal, Satispay etc
	//Now it seems easier to just let credit card, as otherwise we would have to diversify here, maybe create more sigs
		//That is not a problem, problem is in the class diagram
	cardNumber: one Int,
	secureCode: one Int
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
// Is there a more elegant way to do this two (up and down)?
// I know they are conceptually different but they are the same code, does it change??
fact eachPaymentMethodIsOwnedByOneEndUser {
	all p: PaymentMethod | one e: EndUser |
		e.paymentMethod = p 
}

fact eachPaymentMethodIsOwnedByOneEndUser {
	all: e1, e2: EndUser | e1 != e2 => // given two different endUsers
		e1.paymentMethod != e2.paymentMethod
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
	//Makes sense to Marcos 
	
fact eachReminderAssociatedToOneBooking {
	all r: Reminder | one b: Booking |
		r.booking = b
}
// Is there a more elegant way to do this two (up and down)?
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

	//I know that this is fine, but what if you register your dads' card and so do he?
fact everyPaymentMethodIsDifferent {
	all e1, e2: EndUser | e1 != e2 => // given two different endUsers
		e1.paymentMethod != e2.paymentMethod
}
	//Tought about differentiating vehicles but the same argument can be applied
	//Tried to think about examples but only came up with trivial stuff 
		//Users calendar must be different for example
		
//all CPMS constraints...

fact oneCPOperStation{
	all cpo1, cpo2: CPO | cpo1 != cpo2 => //For every two different CPO
		cpo1.chargingStation not in cpo2.chargingStation //Their stations must be different
}
	//idk if its right, as should be like for each chargingStation of cpo1
	








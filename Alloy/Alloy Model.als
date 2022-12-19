//-------------------------------------------------------------------------------------//
//------------------------------------Signatures------------------------------------//
//-------------------------------------------------------------------------------------//

//------------------------------------USERS----------------------------------------//
abstract sig User {
	id: one Int
}{id > 0}

sig End-User extends User {
	paymentMethod: one PaymentMethod,
	calendar: lone Calendar,
	vehicles: some Vehicle,
	bookings: some Booking,
	charges: some Charge
}{id > 0}

sig CPO extends User {
	listDSO: some DSO,
	chargingStations: some ChargingStation
}{id > 0}

//-------------------------------------eMSS-----------------------------------------//
abstract sig Notification {
	end-user: one End-User,
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
	id: one Int,
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











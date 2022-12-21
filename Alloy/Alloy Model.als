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
	vehicles: set Vehicle, 
	bookings: set Booking, 
	charges: set Charge 
}{id > 0}

sig CPO extends User {
	listDSO: some DSO,
	chargingStations: some ChargingStation
}{id > 0}

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
	id: one Int
}{id > 0}

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
	id: one Int,
	location: one Location,
	cost: one CostTable,
	chargingSockets: some ChargingSocket,
	listDSO: some DSO //maybe we could remove this and let it be only in the CSO
}{id > 0}

sig ChargingSocket {
	id: one Int,
	isOccupied: one Boolean,
	powerSupplied: one Int,
	type: one ChargingSocketType
}{id > 0 and powerSupplied>0}

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

//-------------------------------------util types------------------------------------//
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

fact eachUserHasUniqueId {
	no disj u1, u2 : User | u1.id = u2.id
}

fact eachVehicleOwnedByOneEndUser {
	all v: Vehicle | one e: EndUser |
		v in e.vehicles
}

fact eachVehicleHasUniqueId {
	no disj v1, v2 : Vehicle | v1.id = v2.id
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

//all "distinct" constraints...

fact everyPaymentMethodIsDifferent {
	all e1, e2: EndUser | 
		e1 != e2 implies e1.paymentMethod != e2.paymentMethod
}
	

//all CPMS constraints...

fact eachChargingStationHasUniqueId {
	no disj c1, c2 : ChargingStation | c1.id = c2.id
}

fact eachChargingSocketHasUniqueId {
	no disj c1, c2 : ChargingSocket | c1.id = c2.id
}

fact oneCPOperStation{
	all cpo1, cpo2: CPO | all cs1,cs2: ChargingStation |
		(cpo1 != cpo2 and 
		cs1 in cpo1.chargingStations and 
		cs2 in cpo2.chargingStations) 
		implies	cs1 != cs2
}
//i think that the below fact (arrow down \|/) implies the above (arrow up /|\)
//but not vice versa
//in the above there could exist a case in which a cs is not owned by anyone
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

fact sameDSOList {
	all c: CPO | all s: ChargingStation |
		s in c.chargingStations implies s.listDSO = c.listDSO
}

//datetime consistences... (or remove datetime)




//redundant instances
//only to not show useless instances in the world

fact noRedundantLocations {
	all l: Location | one c: ChargingStation |
		c.location = l
}

fact noRedundantDateTime{}

fact noRedundantCostTable{
	all ct: CostTable | one so: SpecialOffer | one s: ChargingStation |
		ct = s.cost or ct = so.prices
}

fact noRedundantInteger{}

fact noRedundantFloat{}

//-------------------------------------------------------------------------------------//
//------------------------------------Assertions-----------------------------------//
//-------------------------------------------------------------------------------------//

//in slides is said that assertions are to verify something we want to rove
//empty space because i have no idea on what we need to verify

//-------------------------------------------------------------------------------------//
//------------------------------------Show------------------------------------------//
//-------------------------------------------------------------------------------------//

pred show {
	#CPO = 2
	//#ChargingStation = 4	//something wrong in declaring this
					//maybe some fact is preventing having more stations than CPO
	#EndUser = 4
	#DSO = 3
}

run show for 10

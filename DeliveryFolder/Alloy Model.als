//----------Signatures----------//

//------------USERS-------------//
abstract sig User {}

sig EndUser extends User {
	paymentMethod: one PaymentMethod,
	calendar: lone Calendar,
	vehicles: set Vehicle, 
	bookings: set Booking, 
	charges: set Charge,
	suggestion: lone Suggestion
}

sig CPO extends User {
	chargingStations: some ChargingStation,
	listDSO: some DSO
}

//-------------eMSS-------------//
sig Vehicle {}

abstract sig Notification {
	dateTime: one DateTime,
}

sig Reminder extends Notification {}

sig ChargingEnd extends Notification {
	charge: one Charge
}

sig Suggestion extends Notification {
	chargingStation: some ChargingStation
}

sig Booking {
	startTime: one DateTime,
	endTime: one DateTime,
	chargingSocket: one ChargingSocket,
	reminder: one Reminder
}

sig PaymentMethod {}

sig Payment {
	isPayed: one Boolean,
	paymentMethod: one PaymentMethod
}

//-------------CPMS-------------//
sig ChargingStation {
	location: one Location,
	cost: one CostTable,
	chargingSockets: some ChargingSocket,
	connectedDSO: one DSO, 
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

//--------shared classes--------//
sig Charge {
	startTime: one DateTime,
	endTime: one DateTime,,
	payment: one Payment,
	chargingSocket: one ChargingSocket 
}

//-------external classes-------//
sig Calendar {}

sig DSO {}

//------Defining new types------//
abstract sig ChargingSocketType {}
one sig SLOW extends ChargingSocketType {}
one sig FAST extends ChargingSocketType {}
one sig RAPID extends ChargingSocketType {}

abstract sig Boolean {}
one sig TRUE extends Boolean {}
one sig FALSE extends Boolean {}

sig DateTime {
	i: one Int
}{i > 0}

sig Location {}

sig CostTable {}

sig Float {}

//------------Facts-------------//

//-------eMSS constraints-------//
fact eachEndserHasOnePaymentMethod {
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

fact eachReminderHasDateTime {
	all r: Reminder | one dt: DateTime |
		r.dateTime = dt
}

fact noSharingReminders {
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
		c in e.charges
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

fact eachChargePayedByProperUser {
	all c: Charge | all e: EndUser |
		c in e.charges implies
		c.payment.paymentMethod in e.paymentMethod
}

fact noSharingSuggestion {
	all e1, e2: EndUser |
		e1 != e2 implies
		(e1.suggestion != e2.suggestion)
}

fact oneChargeToOneChargingEnd {
	all c: ChargingEnd | one ch: Charge|
		c.charge = ch
}

fact noSharingCharge {
	all ch1, ch2: ChargingEnd |
		ch1 != ch2 implies
		(ch1.charge != ch2.charge)
}

fact rightTimeChargingEnd {
	all ce: ChargingEnd | all c: Charge | 
		ce.charge = c implies ce.dateTime = c.endTime
}

fact everyPaymentMethodIsDifferent {
	all e1, e2: EndUser | 
		e1 != e2 implies e1.paymentMethod != e2.paymentMethod
}

//----------CPMS constraints----------//
fact eachStationIsOwnedByOneCPO {
	all s: ChargingStation | one c: CPO |
		s in c.chargingStations
}

fact eachStationConnectedToALegalDSO {
	all s: ChargingStation | all c: CPO | all d: DSO |
		(d = s.connectedDSO and s in c.chargingStations) 
		implies (d in c.listDSO)
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

fact eachSpecialOfferBelongsToOneChargingStation {
	all spo: SpecialOffer | one ch: ChargingStation |
		spo in ch.listSpecialOffers
}

fact noSharingSpecialOffers {
	all ch1, ch2: ChargingStation |
		ch1 != ch2 implies
		((ch1.listSpecialOffers) not in ch2.listSpecialOffers)
}

fact noWrongDateTimeSpecialOfffer {
	all sp: SpecialOffer |
		sp.startTime != sp.endTime
}

fact noSameCostTableChargingStations {
	all cs1, cs2: ChargingStation |
		(cs1 != cs2 implies
		cs1.cost != cs2.cost) 
}

fact noSameCostTableSpecialOffer {
	all sp1, sp2: SpecialOffer |
		(sp1 != sp2 and !(sp1.startTime.i > sp2.endTime.i or sp1.endTime.i < sp2.startTime.i))
		implies sp1.prices != sp2.prices
}

fact noSameCostTableBetween {
	all sp: SpecialOffer | all cs: ChargingStation |
		sp.prices != cs.cost
}

//-----DateTime Consistence-----//
fact uniqueDateTime {
	all d1, d2: DateTime | d1 != d2 implies d1.i != d2.i
}

fact specialOffersTimeConsistence {
	all s: SpecialOffer | s.startTime.i < s.endTime.i
}

fact bookingsTimeConsistence {
	all b: Booking | b.startTime.i < b.endTime.i
}

fact chargingsTimeConsistence {
	all c: Charge | c.startTime.i < c.endTime.i 
}

fact noChargingInSameTimespace{
	all c1,c2: Charge | 
		(c1 != c2 and c1.chargingSocket = c2.chargingSocket)
		implies (c1.startTime.i > c2.endTime.i or c1.endTime.i < c2.startTime.i)
}

fact noBookingInSameTimespace{
	all b1,b2: Booking | 
		(b1 != b2 and b1.chargingSocket = b2.chargingSocket)
		implies (b1.startTime.i > b2.endTime.i or b1.endTime.i < b2.startTime.i)
}

//the only case in which a booking can overlap a charge is that it is done by same user
fact noBookingInSameTimespaceAsCharge {
	all b: Booking | all c: Charge | all e: EndUser |
		(b.chargingSocket = c.chargingSocket and
		!(b.startTime.i > c.endTime.i or b.endTime.i < c.startTime.i))
		implies (b in e.bookings and c in e.charges)
}

//user cannot do a charge and a booking in same timespace unless is the charge associated with that booking
fact noOverlappingChargesOrBookingsOfUser{
	all b: Booking | all c: Charge | all e: EndUser |
		(b in e.bookings and c in e.charges and b.chargingSocket != c.chargingSocket) 
		implies (b.startTime.i > c.endTime.i or b.endTime.i < c.startTime.i)
}

//------Redundant instances-----//
fact noRedundantLocations {
	all l: Location | one c: ChargingStation |
		c.location = l
}

fact noRedundantDSO {
	all d: DSO | some c: CPO |
		d in c.listDSO
}

//-------------Show-------------//

pred show {
	#CPO = 3
	#ChargingStation = 3
	#EndUser = 3
	#DSO = 4
	#ChargingSocket = 4
	#Booking = 2
	#Reminder = 2
	#Charge = 2
	#ChargingEnd = 2
	#Suggestion = 2
}

run show for 10

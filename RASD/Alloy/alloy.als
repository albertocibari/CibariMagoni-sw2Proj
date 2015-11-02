enum TaxiStatus{
	AVAILABLE,
	NON_AVAILABLE,
	OFFLINE
}

enum RequestStatus{
	WAITING,
	RUNNING, 
	COMPLETED
}

sig User{
	request: set Request
}

sig TaxiDriver extends User{
	status:  one TaxiStatus
}

sig Date{}

sig Location{}

sig CityZone{
	borders: some Location,
	queue: one Queue
}{
	#borders >= 3 /*Each zone must have at least three points(three locations)*/
}

sig Queue{ 
	maxQueueLength: one Int, 	
	zone: one CityZone, 
	taxiList: set TaxiDriver 
	} { 
	#taxiList <= maxQueueLength 
	maxQueueLength >= 0 
}

sig TrackLog{
	taxiDriver: one TaxiDriver,
	date: one Date,
	location: set Location
}

sig Request{
	requestStatus: one RequestStatus,
	originLocation: one Location,
	private destinationLocation: lone Location,
	taxiDriver: one TaxiDriver,
    user: one User
}{
	originLocation != destinationLocation
}

sig Reservation extends Request{
	destination: one Location,
} {
	originLocation != destination
}

/*Every cityZone has only one queue and every queue refers to only one cityZone*/
fact AssociationQueueZone{
	all q: Queue,  z: CityZone | 
		(z.queue = q) <=> (q.zone = z)
}

/*A taxi driver is in at least a queue if and only if his status is 'available'*/
fact AvailableTaxiStatus{
	all t : TaxiDriver | ( t.status = AVAILABLE) 
	<=> (some q : Queue | t in q.taxiList)
}

/*Avoid that a taxi driver is associated to a request that is 
already associated to another taxi driver*/
fact NoBusyRequest{ 
	//no t : TaxiDriver, r : Request | t.request = r && r.taxiDriver != t
	all t : TaxiDriver, r : Request | t.request = r <=> r.taxiDriver = t
}

/*Avoid that a request has associated as a user a taxi driver*/
fact NoUserAsATaxiDriver{ 
	no u : User, t : TaxiDriver, r : Request | r.user = u && u = t
}

/*Each taxi driver can be associated to at most a queue*/
fact AssociationQueueTaxiDriver{ 
	no  q1, q2: Queue,  t: TaxiDriver |
		(q1 != q2 and t in q1.taxiList and t in q2.taxiList)
}

fact AssociationUserRequest{
	all u: User, r: Request | (r.user = u) => r in u.request
}

/*There can not exist two logs that refer to the same taxi driver and the same date*/
fact NoLogSameDayPerTaxiDriver{
	no l1, l2: TrackLog |
		(l1 != l2) and (l1.taxiDriver = l2.taxiDriver) and (l1.date = l2.date)
}

/*
Un user può essere associato a una sola richiesta che è in waiting o running
(stessa cosa per taxi driver)


*/

fact OnlyOneWaitingOrRunningRequestPerUser{
	no u: User,  r1, r2: Request | r1 != r2 && r1.user = u && r2.user = u && 
	((r1.requestStatus = WAITING || r1.requestStatus = RUNNING) 
	&& (r2.requestStatus = WAITING || r2.requestStatus = RUNNING))
}

/* If the status of a request is 'waiting' or 'running', it means that the status of the taxi driver who is
associated to that request must be 'available'*/
fact AvalabilityOfTaxiDriver{
	all r : Request, t : TaxiDriver | (r.requestStatus = WAITING || r.requestStatus = RUNNING) && r.taxiDriver = t
	 => t.status = AVAILABLE 
}

pred show{
	#Request = 3
	#CityZone = 1
}
run show for 10

/*
 * DEFINING SIGNATURES
 */

/*
 * General signatures
 */
sig Date{}
sig Location{}

/*
 * Enum that defines the possible status of a taxi driver 
 * in the system
 */
enum TaxiStatus{
	AVAILABLE,
	NON_AVAILABLE,
	OFFLINE
}

/*
 *	Enum that defines the possible status of a request 
 * in the system
 */
enum RequestStatus{
	WAITING,
	RUNNING, 
	COMPLETED
}

sig User{
	request: set Request
}

sig TaxiDriver{
	request: set Request,
	status:  one TaxiStatus
}

sig CityZone{
	borders: set Location,
	queue: one Queue
}{ 
	//Each zone must have at least three points (three locations)
	#borders >= 3 
}

/*
 * Signature defining the queue associated to a CityZone
 * and containing the list of the taxi in the zone
 */
sig Queue{ 
	maxQueueLength: one Int, 	
	zone: one CityZone, 
	taxiList: set TaxiDriver 
} { 
	//The number of taxi must be lesser
	//than the maximum length of the queue
	#taxiList <= maxQueueLength 

	//The maximum length of the queue must be equal or greater than 0
	maxQueueLength >= 0 
}

sig TrackLog{
	taxiDriver: one TaxiDriver,
	date: one Date,
	location: set Location
}

/*
 * Signature defining a request with its associations
 * with the users and the locations
 */
sig Request{
	requestStatus: one RequestStatus,
	originLocation: one Location,
	private destinationLocation: lone Location,
	taxiDriver: lone TaxiDriver,
    user: one User
}{
	originLocation != destinationLocation
}

sig Reservation extends Request{
	destination: one Location,
} {
	originLocation != destination
}


/*
 * DEFINING FACTS
 */

/*
 * Every cityZone has only one queue and every queue refers
 * to only one cityZone
 */
fact AssociationQueueZone{
	all q: Queue,  z: CityZone | 
		(z.queue = q) iff (q.zone = z)
}

/*
 * A taxi driver is in only a queue 
 * if and only if his status is 'available'
 */
fact AvailableTaxiStatus{
	all t : TaxiDriver | 
		( t.status = AVAILABLE) iff (
			one q : Queue | t in q.taxiList
		)
}

/*
 * If a request is associated to a taxi driver, then the 
 * taxi driver must be associated to that request
 */
fact AssociationTaxiRequest{ 
	all t : TaxiDriver, r : Request | 
		(r.taxiDriver = t) iff (r in t.request)
}

/*
 * If a request is associated to a user, then the user 
 * must be associated to that request
 */
fact AssociationUserRequest{
	all u: User, r: Request | 
		(r.user = u) iff (r in u.request) 
}

/*
 * There can not exist two logs that refer
 * to the same taxi driver and the same date
 */
fact NoLogSameDayPerTaxiDriver{
	no l1, l2: TrackLog |
		(l1 != l2) and (l1.taxiDriver = l2.taxiDriver) and (l1.date = l2.date)
}

/*
 * A user can be associated to only a request 
 * which status is 'running' or 'waiting'
 */
fact OnlyOneWaitingOrRunningRequestPerUser{
	no u: User,  r1, r2: Request |
		(r1 != r2) and (r1.user = u) and (r2.user = u) and
		(
			(r1.requestStatus = WAITING or r1.requestStatus = RUNNING) 
			and (r2.requestStatus = WAITING or r2.requestStatus = RUNNING)
		)
}

/*
 * A taxi driver can be associated to only a request 
 * which status is 'running'
 */
fact OnlyOneWaitingOrRunningRequestPerTaxi{
	no t : TaxiDriver,  r1, r2: Request |
		(r1 != r2) and (r1.taxiDriver = t) and (r2.taxiDriver = t) and
		(r1.requestStatus = RUNNING and r2.requestStatus = RUNNING)
}

/* 
 * If the status of a request is 'running', it means that 
 * the status of the taxi driver who is associated 
 * to that request must be 'non available'. 
 * If the status of the taxi driver is 'non available'
 * then there must be only one request which is 'running'
 * assoicated to that driver
*/
fact AvalabilityOfTaxiDriver{
	all r : Request, t : TaxiDriver | 
		(r.requestStatus = RUNNING) and (r.taxiDriver = t) 
		implies (t.status = NON_AVAILABLE)
	all t : TaxiDriver | 
		t.status = NON_AVAILABLE
		implies (one r : Request |r.requestStatus = RUNNING and (r.taxiDriver = t))
}

/* 
 * If the status of a taxi driver is 'non available' or 'offline'
 * it means that he isn't in any queue of the city zones.
*/
fact taxiNotAvailableInQueues{
	all t : TaxiDriver |
		(t.status = NON_AVAILABLE or  t.status = OFFLINE) 
		implies ( no q: Queue |(t in q.taxiList)	)
}

/* 
 * If the status of a taxi driver is 'offline'
 * it means that he is not associated to any request which 
 * status is 'running' or 'waiting'
*/
fact taxiNotAvailableInQueues{
	all t : TaxiDriver |
		(t.status = OFFLINE) implies (
			no r: Request |( t = r.taxiDriver) and 
			(r.requestStatus = RUNNING or r.requestStatus = WAITING)
		)
}

/*
 * If the status of a request is 'waiting',
 * it means that there are no taxi drivers associated to.
 * If the status of the request is 'running' or 'completed',
 * there is only one taxi driver who is associated to.
*/

fact TaxiRequestAssociationWaiting{
	all r : Request | (r.requestStatus = WAITING)
		implies (no t: TaxiDriver | r.taxiDriver = t and r in t.request)
	all r : Request | (r.requestStatus = RUNNING 
		or r.requestStatus = COMPLETED)
			implies (one t: TaxiDriver | r.taxiDriver = t and r in t.request)
}


pred showCompeteScenario{
}

run showCompeteScenario

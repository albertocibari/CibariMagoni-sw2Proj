/*
 * DEFINING SIGNATURES
 */

/*
 * General signatures
 */
sig Date{}
sig Location{}

/*
 * Enum that defines the possible status of a taxi driver in the system
 */
enum TaxiStatus{
	AVAILABLE,
	NON_AVAILABLE,
	OFFLINE
}

/*
 *	Enum that defines the possible status of a request in the system
 */
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

sig CityZone{
	borders: set Location,
	queue: one Queue
}{
	#borders >= 3 // Each zone must have at least three points (three locations)
}

/*
 * Signature defining the queue associated with a CityZone
 * and containing the list of the taxi in the zone
 */
sig Queue{ 
	maxQueueLength: one Int, 	
	zone: one CityZone, 
	taxiList: set TaxiDriver 
} { 
	// The number of taxi must be lesser than the maximum length of the queue
	#taxiList <= maxQueueLength 

	// The maximum length of the queue must be equal or greater than 0
	maxQueueLength >= 0 
}

sig TrackLog{
	taxiDriver: one TaxiDriver,
	date: one Date,
	location: set Location
}

/*
 * Signature defining a request with its associations with the users
 * and the locations
 */
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


/*
 * DEFINING FACTS
 */

/*
 * Every cityZone has only one queue and every queue refers to only one cityZone
 */
fact AssociationQueueZone{
	all q: Queue,  z: CityZone | 
		(z.queue = q) <=> (q.zone = z)
}

/*
 * A taxi driver is in at least a queue if and only if his status is 'available'
 */
fact AvailableTaxiStatus{
	all t : TaxiDriver | 
		( t.status = AVAILABLE) 	<=> (
			some q : Queue | t in q.taxiList
		)
}

/*
 * Avoid that a taxi driver is associated to a request that is 
 * already associated to another taxi driver
 */
fact NoBusyRequest{ 
	all t : TaxiDriver, r : Request |
		(t.request = r) <=> (r.taxiDriver = t)
}

/*
 * Avoid that a request has associated as a user a taxi driver
 */
fact NoUserAsATaxiDriver{ 
	no u : User, t : TaxiDriver, r : Request | 
		(r.user = u) and (u = t)
}

/*
 * Each taxi driver can be associated to at most a queue
 */
fact AssociationUserRequest{
	all u: User, r: Request | 
		(r.user = u) => (r in u.request)
}

/*
 * If a request is assocuiated to a user, then the user must be associated to that request
 */
fact AssociationUserRequest{
	all u: User, r: Request | 
		(r.user = u) => (r in u.request) and (r in u.request) => (r.user = u)
}

/*
 * There can not exist two logs that refer to the same taxi driver and the same date
 */
fact NoLogSameDayPerTaxiDriver{
	no l1, l2: TrackLog |
		(l1 != l2) and (l1.taxiDriver = l2.taxiDriver) and (l1.date = l2.date)
}

/*
 * A user can only be associated to a request if it is in the WAITING or RUNNING status
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
 * If the status of a request is 'RUNNING', it means that the status 
 * of the taxi driver who is associated to that request must be 'NON_AVAILABLE'
*/
fact AvalabilityOfTaxiDriver{
	all r : Request, t : TaxiDriver | 
		(r.requestStatus = RUNNING) and (r.taxiDriver = t) => (t.status = NON_AVAILABLE)
}

/* 
 * If the status of a taxi driver is 'NON_AVAILABLE' or 'OFFLINE'
 * it means that he isn't in any queue of the city zones.
*/
fact taxiNotAvailableInQueues{
	all t : TaxiDriver |
		(t.status = NON_AVAILABLE or  t.status = OFFLINE) =>(
			no q: Queue |(t in q.taxiList)
		)
}

/* 
 * If the status of a taxi driver is 'OFFLINE'
 * it means that he isn't associated to any request
*/
fact taxiNotAvailableInQueues{
	all t : TaxiDriver |
		(t.status = OFFLINE) =>(
			no r: Request |( t = r.taxiDriver)
		)
}

pred showEasyVersion{

	#CityZone = 2

}

run showEasyVersion

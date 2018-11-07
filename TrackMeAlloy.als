open util/integer
open util/boolean
open util/time

sig Username{}
sig CF {}
sig VAT {}

abstract sig RegisteredUser {
	username: one Username,
}

sig User extends RegisteredUser {
	cf: one CF,
	data: some Record,
	/* SUPERFLUO
	age: one Int,
	gender: one Bool,
	height: one Int, //unità di misura in cm
	weight: one Int, //unità di misura ettogrammi
	*/
//	automated_sos: one Bool
}

sig ThirdParty extends RegisteredUser {
	vat: one VAT,
	// For simplicity we consider only accepted requests
	positive_requests: some Request
}

// pred makeRequest

sig HealthStatus {
	heartBeat: lone Int,
	bloodPressure: lone Int,
	bodyTemperature: lone Int, 
	stepCounter: lone Int
}

sig Position {
	latitude: one Int,
	longitude: one Int
}

sig Record {
	timestamp: one Time,
	location: lone Position,
	health: one HealthStatus,
	anon_id: one Int // there exists a 1-1 relation between User and id
}

/*
sig Data {
	location: lone Position,
	health: lone HealthStatus
}
*/

abstract sig Status {}
	// only one of these can be true
one sig Accepted extends Status{}
one sig Pending extends Status{}
one sig Refused extends Status{}

 abstract sig Request {
	/// ***SUPERFLUO*** request_timestamp: one Time,
	sender: one ThirdParty,

// Data request
/*
	localization: one Bool,
	blood_pressure: one Bool,
	hearth_rate: one Bool,
	body_temperature: one Bool
*/
}

sig UserRequest extends Request {
	receiver: one User,
	status: one Status,
	
// Obtained data: the record will be filled only if 
// 1) the request is accepted
// 2) the request contains the specific type of data
	obtained_data: lone Record
}

sig GroupRequest extends Request{
	restrictions: Restrictions,
	allowed: one Bool,

// Obtained data: these will be filled only if 
// 1) the request is allowed
// 2) the request contains the specific type of data
	obtained_data: some Record
}

sig SubscriptionUserRequest extends UserRequest {
	/// ***SUPERFLUO*** update_interval: one Int
}

sig SubscriptionGroupRequest extends GroupRequest {
	/// ***SUPERFLUO*** update_interval: one Int
}

sig Restrictions {
	location: lone Position,
	radius: lone Int,
	age_max: lone Int,
	age_min: lone Int
}
/*
sig EmergencyRecord extends Record {
	user: one User,
	description: one String,
//mettere controllo sui valori salute
//There exists a 1-1 relation between EmergencyRecord and NHS
	closest_emergency_ward: one NHS
}

sig NHS {
	location: one Position,
	telephone_number: one String
}
*/
sig Run {
	organizer: one User,
	path: one Path,
	start_time: one Time,
	end_time: one Time,
	max_participants: one Int,
	enrolled_users: set User,
	participantsNumber: one Int,
	started: one Bool,
	num_spectators: one Int
}

sig Path {
	starting_point: one Position,
	intermediate_points: some Position,
	ending_point: one Position
}








// FACTS
//lo username di ogni utente è unico
fact UniqueUsername{
	no disjoint u1, u2: RegisteredUser | u1.username = u2.username
}

fact UniqueCf{
	no disjoint u1,u2: User | u1.cf = u2.cf}

// una richiesta può assumere uno solo tra i valori Accepted, Pending, Refused
fact requestConsistency {
	all s: Status | (s = Accepted && s != Pending && s != Refused) || 
			(s != Accepted && s = Pending && s != Refused) ||
			(s != Accepted && s != Pending && s = Refused) 
}

fact thirdPartyRequests{
	all t: ThirdParty, r: Request | r in t.positive_requests implies r.sender = t
}

// tutte le richieste che hanno le terze parti sono state accettate 
fact PositiveRequests{
	all t: ThirdParty, r: UserRequest | r in t.positive_requests implies r.status = Accepted
	all t: ThirdParty, r: GroupRequest | r in t.positive_requests implies r.allowed.isTrue
}

fact noDataifGroupNotAllowed {
	all g: GroupRequest | g.allowed.isFalse implies no g.obtained_data
}

fact obtainedDataAfterAcceptance {
	all r: UserRequest | (r.status = Accepted implies one r.obtained_data) 
					and r.obtained_data in r.receiver.data
}

// no istanze scollegate
fact linked {
	all h: HealthStatus | some r: Record | h = r.health 
	all p: Position | some r: Restrictions, rec: Record | p = r.location or p = rec.location
	all r: Record | some u:User | r in u.data
	all r: Restrictions | some g: GroupRequest | r = g.restrictions
	//all g: GroupRequest | one t: ThirdParty | g.sender = t
	all p: Path | some r: Run | p = r.path
}

// ID anonimo è unico
fact uniqueAnonID {
	all u1, u2: User, r1, r2: Record | ((r1 in u1.data) and (r2 in u2.data) and u1 != u2) implies r1.anon_id != r2.anon_id
	all u: User, r1, r2: Record | ((r1 in u.data) and (r2 in u.data)) implies r1.anon_id = r2.anon_id
}

// I record di un utente hanno timestamp diversi tra loro
fact uniqueTimestampUser {
	all u: User, r1, r2: Record | ((r1 in u.data) and (r2 in u.data) and (r1 != r2)) implies r1.timestamp != r2.timestamp
}


//tutti i dati che la terza parte richiede sono diversi da 0 e consistenti.devono corrispondere a quell'utente con quel cf
//fact ContainsData{}
//la ricerca di gruppo piò essere fatta solo se il numero di persone è maggiore di mille o di un valore #records

/* EMERGENCY
fact possibleValue{
	all h: HealthStatus | h.heartBeat > 0 && h.bloodPressure > 0 && h.bodyTemperature > 0 && h.stepCounter >= 0
}
*/

// EMERGENCY: l'emergenza è attivata solo se i valori sono sotto una determinata soglia

//l'inizio di una run deve precedere sempre la fine di una run time
fact TimeConstraints{
	all r: Run | gt[r.end_time,r.start_time]
}

//per ogni corsa il numero dei partecipanti è definito cosi
fact PartecipantsNumber{
	all r: Run| r.participantsNumber = #r.enrolled_users
}

//organizer and enrolled user should be different
fact OrganizerNotEnrolled {
	all r: Run | r.organizer not in r.enrolled_users
}

//enrolledusers<=max_partecipants
fact MaxParticipants {
	all r: Run |( r.participantsNumber >= 0 && r.participantsNumber <= r.max_participants)
}

fact numSpectators {
	all r: Run | ((r.started.isTrue and r.num_spectators >= 0) or
			((not r.started.isTrue) and r.num_spectators = 0))
}

fact minPartecipants {
	all r: Run | (r.started.isTrue implies r.participantsNumber >= 2)
}

//mettere predicato per viewRun? in caso con postcondizione che il numero degli spectators è +1
// live run can be seen only if the run is already started

//tutti gli intermediate points diversi da starting and ending points
fact points {
	all pa: Path | (pa.starting_point not in pa.intermediate_points &&
			pa.ending_point not in pa.intermediate_points)
}







// PREDICATES

pred addRecord[r: Record, u: User] {
	u.data = u.data + r
}

/*
pred newRequest[t: ThirdParty, u: User, r: Request] {
	t.
}

*/
pred acceptRequest[r: UserRequest] {
	r.status = Pending implies r.status = Accepted
	r in r.sender.positive_requests
}

pred refuseRequest[r: UserRequest] {
	r.status = Pending implies r.status = Refused
	r not in r.sender.positive_requests
}


pred isUserEnrolled [r: Run, u: User]{
	u  in r.enrolled_users
}

pred entriesAvailable[r: Run]{
	r.participantsNumber < r.max_participants
}

pred enrollToRun[r, r': Run, u: User]{
	// preconditions
	r.started = False
	entriesAvailable [r]
	not isUserEnrolled [r, u]
	// postconditions
	r'.enrolled_users = r.enrolled_users + u
	isUserEnrolled[r', u]
	r'.participantsNumber <= r.max_participants
	(all u': User| u' in r.enrolled_users implies u' in r'.enrolled_users)
}

pred viewLiveRun[r, r': Run]{
	// precondition
	r.started = True
	// postcondition
	r'.num_spectators = r.num_spectators + 1
}

pred createRun[r: Run, o: User, p: Path, st, et: Time, max: Int]{
	// postconditions
	r.organizer = o
	r.path = p
	r.start_time = st
	r.end_time = et
	r.max_participants = max
	one r': Run | (r'.start_time = r.start_time && r'.end_time = r.end_time && r'.path = r.path &&
			r'.max_participants = r.max_participants)
	r.started = False
	no u: User | u in r.enrolled_users
}

pred show{
//	#Record >= 1
	#User >= 6
	#UserRequest >= 2
//	#User>0 and #User<5
//	#User.data=2
	#ThirdParty >= 1
//	#ThirdParty.accepted_requests<5
	#Run = 6
}

run acceptRequest for 2

//run refuseRequest for 2

run addRecord for 2

run createRun for 10

run viewLiveRun for 10

run enrollToRun for 10 but exactly 8 User

run show for 10



























	

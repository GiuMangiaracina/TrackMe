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
	automated_sos: one Bool
	/* SUPERFLUO
	age: one Int,
	gender: one Bool,
	height: one Int, //unità di misura in cm
	weight: one Int, //unità di misura ettogrammi
	*/
}

sig ThirdParty extends RegisteredUser {
	vat: one VAT,
	// For simplicity we consider only positive requests
	positive_requests: set Request
}

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

sig Description {}

sig EmergencyRecord extends Record {
	user: one User,
	description: one Description
//mettere controllo sui valori salute
}

abstract sig Status {}
	// only one of these can be true
one sig Accepted extends Status{}
one sig Pending extends Status{}
one sig Refused extends Status{}

abstract sig Request {
	sender: one ThirdParty,
}

sig UserRequest extends Request {
	receiver: one User,
	status: one Status,
	
	// A record is present only if the request is accepted by the user
	obtained_data: lone Record
} {
	(status = Pending or status = Refused) implies no obtained_data
}

sig GroupRequest extends Request{
	restrictions: Restrictions,
	allowed: one Bool,

	// A record is present only if the request is allowed by the system
	obtained_data: some Record
}

sig SubscriptionUserRequest extends UserRequest {}
sig SubscriptionGroupRequest extends GroupRequest {}

sig Restrictions {
	location: lone Position,
	radius: lone Int,
	age_max: lone Int,
	age_min: lone Int
}

sig Run {
	organizer: one User,
	path: one Path,
	start_time: one Time,
	end_time: one Time,
	max_participants: one Int,
	enrolled_users: set User,
	participantsNumber: one Int,
	started: one Bool,
	ended: one Bool,
	num_spectators: one Int
}

sig Path {
	starting_point: one Position,
	intermediate_points: set Position,
	ending_point: one Position
}








// DATA4HELP

// Registration data for the system are unique
fact registrationDataUniqueness {
	// Unique username
	no disjoint u1, u2: RegisteredUser | u1.username = u2.username
	// Unique fiscal code
	no disjoint u1,u2: User | u1.cf = u2.cf
	// Unique VAT
	no disjoint t1,t2: ThirdParty | t1.vat = t2.vat
}

// Request status can have only one of these values: Accepted, Pending or Refused
fact requestConsistency {
	all s: Status | (s = Accepted && s != Pending && s != Refused) || 
			(s != Accepted && s = Pending && s != Refused) ||
			(s != Accepted && s != Pending && s = Refused) 
}

// If a request has no sender, it also has no receiver
fact noSenderNoReceiver {
	all r: Request | no r.sender implies no r.receiver
}

// Accepted/allowed requests are related to the third party that sent them
fact thirdPartyRequests{
	all t: ThirdParty, r: Request | r in t.positive_requests implies r.sender = t
}

// All the request related to a third party have been accepted/allowed 
fact PositiveRequests{
	all t: ThirdParty, r: UserRequest | r in t.positive_requests implies r.status = Accepted
	all t: ThirdParty, r: GroupRequest | r in t.positive_requests implies r.allowed.isTrue
}

// A group request does not contain data if it is not allowed by the system
fact noDataifGroupNotAllowed {
	all g: GroupRequest | g.allowed.isFalse implies no g.obtained_data
}

// If accepted by the user, a user request contains one record of the user who accepted it
fact obtainedDataAfterAcceptance {
	all r: UserRequest | (r.status = Accepted implies one r.obtained_data) 
					and r.obtained_data in r.receiver.data
}

// No unlinked instances
fact noUnlinked {
	all h: HealthStatus | some r: Record | h = r.health 
	all p: Position | some r: Restrictions, rec: Record | p = r.location or p = rec.location
	//all r: Record | some u:User | r in u.data
	all r: Restrictions | some g: GroupRequest | r = g.restrictions
	//all g: GroupRequest | one t: ThirdParty | g.sender = t
	all p: Path | some r: Run | p = r.path
	all d: Description | some e: EmergencyRecord | d = e.description
}


fact uniqueAnonID {
	// Records associated with different users have different anonymous ID
	all u1, u2: User, r1, r2: Record | ((r1 in u1.data) and (r2 in u2.data) and u1 != u2) implies r1.anon_id != r2.anon_id
	// Records associated with the same user have the same anonymous ID
	all u: User, r1, r2: Record | ((r1 in u.data) and (r2 in u.data)) implies r1.anon_id = r2.anon_id
}

// Records associated with the same user have different timestamps
fact uniqueTimestampUser {
	all u: User, r1, r2: Record | ((r1 in u.data) and (r2 in u.data) and (r1 != r2)) implies r1.timestamp != r2.timestamp
}

/* 	NON FUNZIONANO I LIMITI PER GLI INT
fact possibleValues{
	all h: HealthStatus | h.heartBeat > 0 and h.bloodPressure > 0 and h.bodyTemperature > 0 and h.stepCounter >= 0
	all p: Position | p.latitude >= -90 and p.latitude <= 90 and p.longitude >= -180 and p.longitude <= 180 
	all rec: Record | rec.anon_id >= 0
	all res: Restrictions | res.radius > 0 and res.radius < 5000 //km
				and res.age_max >= 18 and res.age_max < 110 and res.age_min >= 18 and res.age_min < 110
	all r: Run | r.max_participants > 0 and r.max_participants < 1000000
				and  r.participantsNumber > 0 and r.participantsNumber < 100000
				and  r.num_spectators > 0 and r.num_spectators < 100000
}
*/

// TRACK4RUN

// The end of a run must happen after its start
fact TimeConstraints{
	all r: Run | gt[r.end_time, r.start_time]
}

// Participant number definition
fact PartecipantsNumber{
	all r: Run| r.participantsNumber = #r.enrolled_users
}

// Organizer and enrolled user must be different
fact OrganizerNotEnrolled {
	all r: Run | r.organizer not in r.enrolled_users
}

// The number of users enrolled for the same run must not exceed the maximum number of participants set by the organizator
fact MaxParticipants {
	all r: Run | ( r.participantsNumber >= 0 and r.participantsNumber <= r.max_participants)
}

// A run can not be finished if it is not started yet
fact noFinishedIfNotSarted {
	all r: Run | (r.ended.isTrue implies r.started.isTrue) and (r.started.isFalse implies r.ended.isFalse)
}


// A run has no spectators if it hasn't started yet or if it has already ended.
fact numSpectators {
	all r: Run | (r.started.isFalse or r.ended.isTrue) implies r.num_spectators = 0
}

// In order for a run to start, there must be at least one user enrolled
fact minPartecipants {
	all r: Run | (r.started.isTrue implies r.participantsNumber >= 1)
}

// Intermediate points are different from the starting and ending points
fact points {
	all pa: Path | (pa.starting_point not in pa.intermediate_points and
			pa.ending_point not in pa.intermediate_points)
}

// AUTOMATED SOS

// L'emergenza è attivata solo se i valori sono sotto una determinata soglia

/*  	NON FUNZIONANO I LIMITI PER GLI INT
fact emergencyIfNeeded {
	all e: EmergencyRecord | e.health.heartBeat < 45 or e.health.heartBeat > 100 //bpm
						or e.health.bloodPressure < 50 or e.health.bloodPressure > 160 //mmHg
						or e.health.bodyTemperature < 33 or e.health.bodyTemperature > 40 //°C
}
*/






// PREDICATES

pred addRecord[r, r': Record, u: User] {
	// preconditions
	//r not in User.data
	// postconditions
	#u.data > 0 implies (r' in u.data and r.anon_id = r'.anon_id)
	u.data = u.data + r
}

pred newRequest[t: ThirdParty, u: User, r: Request] {
	// postconditions
	r.sender = t
	r.receiver = u
	r.status = Pending
}

pred acceptRequest[r, r': UserRequest] {
	// preconditions
	r.status = Pending
	// postconditions
	r'.status = Accepted
	r' in r'.sender.positive_requests
}

pred refuseRequest[r, r': UserRequest] {
	// preconditions
	r.status = Pending
	// postconditions
	r'.status = Refused
	r' not in r'.sender.positive_requests
}


pred isUserEnrolled [r: Run, u: User]{
	u in r.enrolled_users
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
	r.started.isTrue and r.ended.isFalse
	// postcondition 					*** DUBBIO, la nuova r' dovrebbe avere anche tutti gli altri campi uguali a r? ***
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
	#ThirdParty >= 2
	3 >= #UserRequest and #UserRequest >= 2
	3 >= #GroupRequest and #GroupRequest >= 2
//	#ThirdParty.accepted_requests<5
	some u: User | #u.data=3
	#HealthStatus >= 5
	some r, r': Record |  r.health != r'.health
	#EmergencyRecord = 2
	#Run = 3
}


run show for 10

// run addRecord for 4

// run newRequest for 2

// run acceptRequest for 2

// run refuseRequest for 2

// run addRecord for 2

// run createRun for 10

// run viewLiveRun for 10

// run enrollToRun for 10 but exactly 8 User







open util/ordering [Time] as T

sig Time{}
abstract sig LastOperation{}
one sig msg1HonestToIntruder, msg1IntruderToHonest extends LastOperation{}
one sig Track{op: LastOperation lone -> Time}




abstract sig Agent{
	pair: set Agent,
	sharedKey: pair ->Key
}

sig Honest extends Agent{
	sendMsg1: Nonce  -> Honest -> Time,
	sendMsg2: Enc  -> Honest -> Time,
	receivedMsg1: Nonce -> Honest ->Time,
	receivedMsg2: Enc -> Honest ->Time,
	to: Agent lone -> Time,
	from: Agent lone -> Time
}

one sig Intruder extends Agent{
	to: Agent lone -> Time,
	sendMsg1: Nonce  -> Honest -> Time,
	sendMsg2: Enc  -> Honest -> Time,
	receivedMsg1: Nonce -> Honest ->Time,
	receivedMsg2: Enc -> Honest ->Time,
	from: Agent lone -> Time
}

sig Key{}
sig Nonce{}

sig Enc{
	EncryptKey: Key,
	nonce: Nonce
}

pred init [t: Time]{
	no Honest.receivedMsg1.t
	no  Honest.sendMsg1.t
	no  Honest.to.t
	no  Honest.from.t
	no Intruder.receivedMsg1.t
	no Intruder.receivedMsg2.t
	no Intruder.sendMsg1.t
	no Intruder.sendMsg2.t
	no  Intruder.to.t
	no  Intruder.from.t
//	no Enc
}

pred trans[t, t':Time]{
	some a,b:Honest | let n = Nonce | (msg1HonestToIntruder[t, t', a, b, n] and Track.op.t'=msg1HonestToIntruder )  or (msg1IntruderToHonest[t,t',a,b,n] and Track.op.t'=msg1IntruderToHonest) 
}

//Operations

pred msg1HonestToIntruder[t,t':Time, Alice,Bob:Honest, n:Nonce] {
	
	//Pre conditions 


	//Post Conditions

	Alice.to.t'= Alice.to.t + Bob
	Alice.sendMsg1.t'=Alice.sendMsg1.t + n->Bob
	Intruder.receivedMsg1.t'=Intruder.receivedMsg1.t + n->Alice
	Intruder.from.t'= Intruder.from.t + Alice

	//Frame Conditions
	noMessageSentExcept[t, t', Alice, none]
	noMessageReceivedExcept[t,t', none, Intruder]
	
}

pred msg1IntruderToHonest[t,t':Time, Alice,Bob:Honest, n:Nonce]{

	//Pre Conditions
//	n->Alice  in Intruder.receivedMsg1.t
	
	//Post Conditions
	Bob.from.t'=Bob.from.t+Alice
	Bob.receivedMsg1.t'= Bob.receivedMsg1.t + n->Alice
	Intruder.sendMsg1.t'= Intruder.sendMsg1.t + n-> Bob
	Intruder.to.t'=Intruder.to.t + Bob 
	//(Intruder.sendMsg1.t'= Intruder.sendMsg1.t + (Intruder.receivedMsg1.t[n]) ->Bob ) or (Intruder.sendMsg1.t'= Intruder.sendMsg1.t + n-> Bob ) 
	//Frame conditions
	noMessageSentExcept[t, t', none, Intruder]
	noMessageReceivedExcept[t,t', Bob, none]
}


pred msg2HonestToIntruder[t, t': Time, Alice, Bob: Honest, n: Nonce, e: Enc] {

	// Pre conds

	// first message exchange must have occured already, Bob must know nA (nonce of A) 

	// Post conds

	Bob.to.t' = Bob.to.t + Alice
	Bob.sendMsg1.t' = Bob.sendMsg1.t + n->Alice
	Bob.sendMsg2.t' = Bob.sendMsg2.t + e->Alice

	Intruder.receivedMsg1.t' = Intruder.receivedMsg1.t + n->Bob
	Intruder.from.t' = Intruder.from.t + Bob
	// Intruder.to.t' = Intruder.to.t + Alice

	// Frame
	// noRecvToHimself
	noMessageSentExcept[t, t', Bob, none]
	noMessageReceivedExcept[t, t', none, Intruder]
}

pred msg2IntruderToHonest[t, t': Time, Alice, Bob: Honest, n: Nonce, e: Enc] {
	
	// Pre Conditions

	// Intruder has nonce and encrypted message from Bob

	// Post Conditions
	Intruder.sendMsg1.t' = Intruder.sendMsg1.t + n->Alice
	Intruder.sendMsg2.t' = Intruder.sendMsg2.t + e->Alice
	Intruder.to.t' = Intruder.to.t + Alice
	
	Alice.from.t' = Alice.from.t + Bob
	Alice.receivedMsg1.t' = Alice.receivedMsg1.t + n->Bob
	Alice.receivedMsg2.t' = Alice.receivedMsg2.t + e->Bob

	// Frame
	noMessageSentExcept[t, t', none, Intruder]
	noMessageReceivedExcept[t, t', Alice, none]

	
}

//Frame Conditions

pred noMessageSentExcept[t,t':Time, a: set Honest, i:Intruder]{
	all h:Honest - a | h.sendMsg1.t'=h.sendMsg1.t and h.to.t'=h.to.t
	(i=none) implies Intruder.to.t'=Intruder.to.t and Intruder.sendMsg1.t'=Intruder.sendMsg1.t
}

pred noMessageReceivedExcept[t,t':Time, a: set Honest, i:Intruder]{
	all h:Honest - a | h.receivedMsg1.t'=h.receivedMsg1.t and h.from.t'=h.from.t
	(i=none) implies Intruder.from.t'=Intruder.from.t and Intruder.receivedMsg1.t'=Intruder.receivedMsg1.t
}

//Facts

pred AgentFacts{
	all a:Agent | (Agent-a) in a.pair and a not in a.pair
	all a,b: Agent | a in b.pair implies ( b in a.pair and one a.sharedKey[b] and one b.sharedKey[a] and a.sharedKey[b] = b.sharedKey[a])
	all a,b,c: Agent, k:Key | b->k in a.sharedKey and c->k in a.sharedKey implies b=c
//	all a,b,c:Agent, k:Key | b->k in a.sharedKey and Intruder ->k in a.sharedKey implies  ( b->k not in a.sharedKey and  c->k not in a.sharedKey implies b=c)
}


fact{// comentado
	init [T/first]
	all t: Time - T/last | trans [t, T/next[t]]
	all t: Time | all h:Honest | Intruder not in h.from.t and Intruder not in h.to.t 
	all t: Time | all h:Honest | h not in h.to.t and h not in h.from.t
	AgentFacts
}


//Runs


run msg1IntruderToHonest for 5
run msg1HonestToIntruder for 5
run msg2HonestToIntruder for 5 but exactly 2 Honest, 1 Enc
run msg2IntruderToHonest for 5 but exactly 2 Honest, 1 Enc

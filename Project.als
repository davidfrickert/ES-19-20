open util/ordering [Time] as T

sig Time{}
abstract sig LastOperation{}
one sig msg1HonestToIntruder, msg1IntruderToHonest, msg2HonestToIntruder, msg2IntruderToHonest extends LastOperation{}
one sig Track{op: LastOperation lone -> Time}




abstract sig Agent{
	pair: set Agent,
	sharedKey: pair ->  Key
}{
//	all k, k1:Key | k->this in ~sharedKey and k1->this in ~sharedKey implies k=k1
}

sig Honest extends Agent{
	sendMsg1: Nonce  -> Honest -> Time,
	sendMsg2: Enc -> Honest -> Time,
	receivedMsg1: Nonce -> Honest ->Time,
	receivedMsg2: Nonce -> Honest ->Time,
	to: Agent lone -> Time,
	from: Agent lone -> Time
}

one sig Intruder extends Agent{
	to: Agent lone -> Time,
	sendMsg1: Nonce  -> Honest -> Time,
	sendMsg2: Nonce  -> Honest -> Time,
	receivedMsg1: Nonce -> Honest ->Time,
	receivedMsg2: Enc ->Time,
	from: Agent lone -> Time
}

sig Key{}
sig Nonce{}

sig Enc {
	EncryptKey:  Key lone -> Time,
	Text:  Nonce lone -> Time,
	Iden:  Honest lone -> Time
}

pred init [t: Time]{
	no Honest.receivedMsg1.t
	no Honest.sendMsg2.t
	no  Honest.sendMsg1.t
	no Honest.sendMsg2.t
	no  Honest.to.t
	no  Honest.from.t
	no Intruder.receivedMsg1.t
	no Intruder.receivedMsg2.t
	no Intruder.sendMsg1.t
	no Intruder.sendMsg2.t
	no Intruder.to.t
	no Intruder.from.t
	no Enc.EncryptKey.t
	no Enc.Text.t
	no Enc.Iden.t
}

pred trans[t, t':Time]{
	some a,b:Honest, disj n,n1:Nonce, m:Enc | (msg1HonestToIntruder[t, t', a, b, n] and Track.op.t'=msg1HonestToIntruder )  or (msg1IntruderToHonest[t,t',a,b,n] and Track.op.t'=msg1IntruderToHonest) or (msg2HonestToIntruder[t,t',a,b,n, n1, m] and Track.op.t'=msg2HonestToIntruder) 
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
	noEncriptedMessageChangeExcept[t,t',none]
	Intruder.receivedMsg2.t'=Intruder.receivedMsg2.t
	Intruder.sendMsg2.t'=Intruder.sendMsg2.t
	
}

pred msg1IntruderToHonest[t,t':Time, Alice,Bob:Honest, n:Nonce]{

	//Pre Conditions
	Alice in Intruder.from.t
	Alice  in Intruder.receivedMsg1.t [n]
	
	//Post Conditions

	Bob.from.t'=Bob.from.t+Alice
	Bob.receivedMsg1.t'= Bob.receivedMsg1.t + n->Alice
	Intruder.sendMsg1.t'= Intruder.sendMsg1.t + n-> Bob
	Intruder.to.t'=Intruder.to.t + Bob

 
	//Frame conditions
	noMessageSentExcept[t, t', none, Intruder]
	noMessageReceivedExcept[t,t', Bob, none]
	noEncriptedMessageChangeExcept[t,t',none]
	Intruder.receivedMsg2.t'=Intruder.receivedMsg2.t
	Intruder.sendMsg2.t'=Intruder.sendMsg2.t
}

pred msg2HonestToIntruder[t,t':Time, Alice,Bob:Honest, n, n1:Nonce, m:Enc]{
	//Pre Conditions
		
		Alice in Bob.receivedMsg1.t [n]
	//	Alice in Bob.from.t
	//	some Bob.receivedMsg1.t.Alice

	//Post Conditions
	
		m.EncryptKey.t'= m.EncryptKey.t+Alice.sharedKey[Bob]  
		m.Text.t'= m.Text.t+n 
		m.Iden.t'=m.Iden.t+Bob

		Bob.to.t'=Bob.to.t + Alice
		Bob.sendMsg1.t'= Bob.sendMsg1.t + n1->Alice
		Bob.sendMsg2.t'=Bob.sendMsg2.t + m->Alice

		Intruder.from.t'=Intruder.from.t + Bob
		Intruder.receivedMsg1.t'=Intruder.receivedMsg1.t + n1->Bob
		Intruder.receivedMsg2.t'=Intruder.receivedMsg2.t + m
	
	 
		
	//Frame Conditions
		noMessageSentExcept[t, t', Bob, none]
		noMessageReceivedExcept[t,t', none, Intruder]
		noEncriptedMessageChangeExcept[t,t',m]
	
}

pred msg2IntruderToHonest[t, t': Time, Alice, Bob: Honest, n: Nonce, e: Enc] {
	
	// Pre Conditions

	// Intruder has nonce and encrypted message from Bob
	// n funciona por causa do init
//	n in Intruder.receivedMsg1.t.Bob
//	e in Intruder.receivedMsg2.t

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
	noEncriptedMessageChangeExcept[t,t', none]
}


//Frame Conditions

pred noMessageSentExcept[t,t':Time, a: set Honest, i:Intruder]{
	all h:Honest - a | h.sendMsg1.t'=h.sendMsg1.t and h.to.t'=h.to.t and h.sendMsg2.t'=h.sendMsg2.t 
	(i=none) implies Intruder.to.t'=Intruder.to.t and Intruder.sendMsg1.t'=Intruder.sendMsg1.t and Intruder.sendMsg2.t'=Intruder.sendMsg2.t
}

pred noMessageReceivedExcept[t,t':Time, a: set Honest, i:Intruder]{
	all h:Honest - a | h.receivedMsg1.t'=h.receivedMsg1.t and h.from.t'=h.from.t and h.receivedMsg2.t'=h.receivedMsg2.t
	(i=none) implies Intruder.from.t'=Intruder.from.t and Intruder.receivedMsg1.t'=Intruder.receivedMsg1.t and Intruder.receivedMsg2.t'=Intruder.receivedMsg2.t
}

pred noEncriptedMessageChangeExcept[t,t':Time, a:set Enc]{
	all m:Enc - a | m.Text.t'=m.Text.t and m.Iden.t'=m.Iden.t and m.EncryptKey.t'=m.EncryptKey.t
}

//Facts

pred AgentFacts{
	all a:Agent | (Agent-a) in a.pair and a not in a.pair
	all a,b: Agent | a in b.pair implies ( b in a.pair and one a.sharedKey[b] and one b.sharedKey[a] and a.sharedKey[b] = b.sharedKey[a])
	all a,b,c: Agent, k:Key | b->k in a.sharedKey and c->k in a.sharedKey implies b=c
 //	all a: Agent, k, k1:Key | k->a in a.(~sharedKey) and k1->a in a.(~sharedKey) implies k=k1	
}


fact{
	init [T/first]
	all t: Time - T/last | trans [t, T/next[t]]
	all t: Time | all h:Honest | Intruder not in h.from.t and Intruder not in h.to.t 
	all t: Time | all h:Honest | h not in h.to.t and h not in h.from.t
	AgentFacts
}

//Runs


//run msg1IntruderToHonest for 5
run msg1HonestToIntruder for 3 but exactly 4 Time 
run msg2HonestToIntruder for 3

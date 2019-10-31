open util/ordering [Time] as T

sig Time{}
abstract sig LastOperation{}
one sig msg1HonestToIntruder, msg1IntruderToHonest, msg2HonestToIntruder, msg2IntruderToHonest, msg3HonestToIntruder, msg3IntruderToHonest extends LastOperation{}
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
	receivedMsg2: Enc -> Honest ->Time,
	to: Agent -> Time,
	from: Agent  -> Time
}

one sig Intruder extends Agent{
	to: Agent -> Time,
	sendMsg1: Nonce  -> Honest -> Time,
	sendMsg2: Enc -> Honest -> Time,
	receivedMsg1: Nonce -> Honest ->Time,
	receivedMsg2: Enc ->Time,
	from: Agent -> Time
}

sig Key{}
sig Nonce{}

sig Enc {
	EncryptKey:  Key lone -> Time,
	Text:  Nonce lone -> Time,
	Iden:  Honest lone -> Time
}

pred init [t: Time]{
	no  Honest.receivedMsg1.t
	no  Honest.receivedMsg2.t
	no  Honest.sendMsg1.t
	no  Honest.sendMsg2.t
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
	some  disj a,b:Honest | one disj n,n1:Nonce, m:Enc {   (msg1HonestToIntruder[t, t', a, b, n] and Track.op.t'=msg1HonestToIntruder )  
									or (msg1IntruderToHonest[t,t',a,b,n] and Track.op.t'=msg1IntruderToHonest) 
									or (msg2HonestToIntruder[t,t',a,b,n, n1, m] and Track.op.t'=msg2HonestToIntruder)
									or (msg2IntruderToHonest[t,t',a,b,n1,m] and Track.op.t'=msg2IntruderToHonest)
									or (msg3HonestToIntruder[t,t',a,b,n1,m] and Track.op.t'=msg3HonestToIntruder)
									or (msg3IntruderToHonest[t,t',a,b,m] and Track.op.t'=msg3IntruderToHonest)   } 
}

//Operations

pred msg1HonestToIntruder[t,t':Time, Alice,Bob:Honest, n:Nonce] {
	
	//Pre conditions 

 	init[t]
	
	//Post Conditions

	Alice.to.t'= Alice.to.t + Bob
	Alice.sendMsg1.t'=Alice.sendMsg1.t + n->Bob
	Intruder.receivedMsg1.t'=Intruder.receivedMsg1.t + n->Alice
	Intruder.from.t'= Intruder.from.t + Alice
	

	//Frame Conditions
	noMessageType1SentExcept[t, t', Alice, none]
	noMessageType2SentExcept[t, t', none, none]
	noMessageType1ReceivedExcept[t, t', none, Intruder]
	noMessageType2ReceivedExcept[t, t', none, none]
	noEncriptedMessageChangeExcept[t, t', none]
	noAgentToChangeExcept[t,t',Alice,none]
	noAgentFromChangeExcept[t,t',none, Intruder]
}

pred msg1IntruderToHonest[t,t':Time, Alice,Bob:Honest, n:Nonce]{

	//Pre Conditions
//	Bob not in Bob.receivedMsg1.t[n]
	Bob not in Intruder.to.t
	Bob in Alice.sendMsg1.t [n]
	Bob in Alice.to.t
	
	
	//Post Conditions

	Bob.from.t'=Bob.from.t+Alice
	Bob.receivedMsg1.t'= Bob.receivedMsg1.t + n->Alice
	Intruder.sendMsg1.t'= Intruder.sendMsg1.t + n-> Bob or 
	Intruder.to.t'=Intruder.to.t + Bob

 
	//Frame conditions
	noMessageType1SentExcept[t, t', none, Intruder]
	noMessageType2SentExcept[t, t', none, none]
	noMessageType1ReceivedExcept[t,t', Bob, none]
	noMessageType2ReceivedExcept[t,t',none,none]
	noEncriptedMessageChangeExcept[t,t',none]
	noAgentToChangeExcept[t,t',none, Intruder]
	noAgentFromChangeExcept[t,t',Bob, none]

}

pred msg2HonestToIntruder[t,t':Time, Alice,Bob:Honest, n, n1:Nonce, m:Enc]{
	//Pre Conditions

		Alice in Bob.receivedMsg1.t [n]
		Alice in Bob.from.t
		no Intruder.receivedMsg2.t
		m not in Intruder.receivedMsg2.t 
	
	
	//Post Conditions
	
		m.EncryptKey.t'= m.EncryptKey.t+Bob.sharedKey[Alice]  
		m.Text.t'= m.Text.t + n 
		m.Iden.t'=m.Iden.t + Bob

		Bob.to.t'=Bob.to.t + Alice
		Bob.sendMsg1.t'= Bob.sendMsg1.t + n1->Alice
		Bob.sendMsg2.t'=Bob.sendMsg2.t + m->Alice

		Intruder.from.t'=Intruder.from.t + Bob
		Intruder.receivedMsg1.t'=Intruder.receivedMsg1.t + n1->Bob
		Intruder.receivedMsg2.t'=Intruder.receivedMsg2.t + m
	
	 
		
	//Frame Conditions
		noMessageType1SentExcept[t, t', Bob, none]
		noMessageType2SentExcept[t, t', Bob, none]
		noMessageType2ReceivedExcept[t,t',none, Intruder]
		noMessageType1ReceivedExcept[t,t', none, Intruder]
		noEncriptedMessageChangeExcept[t,t',m]
		noAgentToChangeExcept[t,t',Bob,none]
		noAgentFromChangeExcept[t,t',none, Intruder]
}

pred msg2IntruderToHonest[t, t': Time, Alice,Bob: Honest, n: Nonce, e: Enc] {
	
	// Pre Conditions

	 Bob in Intruder.receivedMsg1.t [n]
   	 e in Intruder.receivedMsg2.t
	 Alice not in Intruder.sendMsg1.t[n]
	 Alice not in Intruder.to.t

	// Post Conditions
	
	Intruder.sendMsg1.t' = Intruder.sendMsg1.t + n->Alice
	Intruder.sendMsg2.t' = Intruder.sendMsg2.t + e->Alice
	Intruder.to.t' = Intruder.to.t + Alice
	
	Alice.from.t' = Alice.from.t + Bob

	Alice.receivedMsg1.t' = Alice.receivedMsg1.t + n->Bob
	Alice.receivedMsg2.t' = Alice.receivedMsg2.t + e->Bob

	// Frame
	noMessageType1SentExcept[t, t', none, Intruder]
	noMessageType2SentExcept[t, t', none, Intruder]
	noMessageType1ReceivedExcept[t, t', Alice, none]
	noMessageType2ReceivedExcept[t,t', Alice, none]
	noEncriptedMessageChangeExcept[t,t', e]
	noAgentToChangeExcept[t,t',none, Intruder]
	noAgentFromChangeExcept[t,t',Alice, none]
}

pred msg3HonestToIntruder[t, t': Time, Alice, Bob: Honest, n: Nonce, m: Enc]{

	//PreConditions
		Bob in Alice.receivedMsg1.t [n]
	      	Bob in Alice.from.t
		Bob in Alice.receivedMsg2.t [m]
		Bob not in Alice.sendMsg2.t [m]
	//	Alice not in m.Iden.t	
	
	//PostConditions
		m.EncryptKey.t'= Alice.sharedKey[Bob]  
		m.Text.t'=  n 
		m.Iden.t'= Alice
		
		Alice.sendMsg2.t'=Alice.sendMsg2.t+m->Bob
		Alice.to.t'=Alice.to.t + Bob
		//reminder: Alice forgets n of m

		Intruder.from.t'=Intruder.from.t + Alice
		Intruder.receivedMsg2.t'=Intruder.receivedMsg2.t + m
		

	//Frame
	noMessageType1SentExcept[t, t', none, none]
	noMessageType2SentExcept[t, t', Alice, none]
	noMessageType1ReceivedExcept[t, t', none,  none]
	noMessageType2ReceivedExcept[t,t',none, Intruder]
	noEncriptedMessageChangeExcept[t,t',m]
	noAgentToChangeExcept[t,t',Alice,none]
	noAgentFromChangeExcept[t,t',none, Intruder]

}

pred msg3IntruderToHonest[t, t': Time, Alice, Bob: Honest, e: Enc] {
	
	// Pre Conditions
	e in Intruder.receivedMsg2.t
//	Alice in Intruder.from.t
	some Alice.sendMsg2.t


	// Post Conditions
	Intruder.sendMsg2.t' = Intruder.sendMsg2.t + e->Bob
	Intruder.to.t' = Intruder.to.t + Bob
	
	Bob.from.t' = Bob.from.t + Alice
	Bob.receivedMsg2.t' = Bob.receivedMsg2.t + e->Alice

	// Frame
	noMessageType1SentExcept[t, t', none, none]
	noMessageType2SentExcept[t, t', none, Intruder ]
	noMessageType1ReceivedExcept[t, t', none,  none]
	noMessageType2ReceivedExcept[t,t',Bob, none]
	noEncriptedMessageChangeExcept[t,t',none]
	noAgentToChangeExcept[t,t',none, Intruder]
	noAgentFromChangeExcept[t,t',Bob, none]
}


//Frame Conditions

pred noMessageType1SentExcept[t,t':Time, a: set Honest, i:Intruder]{
	all h:Honest - a | h.sendMsg1.t'=h.sendMsg1.t
	(i=none) implies Intruder.sendMsg1.t'=Intruder.sendMsg1.t //and Intruder.sendMsg2.t'=Intruder.sendMsg2.t
}

pred noMessageType2SentExcept[t,t':Time, a: set Honest, i:Intruder]{
	all h:Honest - a |   h.sendMsg2.t'=h.sendMsg2.t 
	(i=none) implies  Intruder.sendMsg2.t'=Intruder.sendMsg2.t
}

pred noMessageType1ReceivedExcept[t,t':Time, a: set Honest, i:Intruder]{
	all h:Honest - a | h.receivedMsg1.t'=h.receivedMsg1.t //and h.receivedMsg2.t'=h.receivedMsg2.t
	(i=none) implies Intruder.receivedMsg1.t'=Intruder.receivedMsg1.t //and Intruder.receivedMsg2.t'=Intruder.receivedMsg2.t
}

pred noMessageType2ReceivedExcept[t,t':Time, a: set Honest, i:Intruder]{
	all h:Honest - a | h.receivedMsg2.t'=h.receivedMsg2.t
	(i=none) implies Intruder.receivedMsg2.t'=Intruder.receivedMsg2.t
}

pred noEncriptedMessageChangeExcept[t,t':Time, a:set Enc]{
	all m:Enc - a | m.Text.t'=m.Text.t and m.Iden.t'=m.Iden.t and m.EncryptKey.t'=m.EncryptKey.t
}

pred noAgentToChangeExcept[t,t':Time, a:set Honest, i:Intruder]{
	all h:Honest - a |  h.to.t'=h.to.t
	(i=none) implies Intruder.to.t'=Intruder.to.t
}

pred noAgentFromChangeExcept[t,t':Time, a:set Honest, i:Intruder]{
	all h:Honest - a | h.from.t'=h.from.t 
	(i=none) implies Intruder.from.t'=Intruder.from.t 
}

//Facts

pred AgentFacts{
	all a:Agent | (Agent-a) in a.pair and a not in a.pair
	all a,b: Agent | a in b.pair implies ( b in a.pair and one a.sharedKey[b] and one b.sharedKey[a] and a.sharedKey[b] = b.sharedKey[a])
	all a,b,c: Agent, k:Key | b->k in a.sharedKey and c->k in a.sharedKey implies b=c
	all  disj a,b,c: Agent |   (a.sharedKey[b] != a.sharedKey[c]) 	
}


fact{
	init [T/first]
	all t: Time - T/last | trans [t, T/next[t]]
	all t: Time | all h:Honest | Intruder not in h.from.t and Intruder not in h.to.t 
	all t: Time | all h:Honest | h not in h.to.t and h not in h.from.t 
	AgentFacts
}

//Runs


run msg3IntruderToHonest for 7 but exactly 8 Time
run msg1HonestToIntruder for 7 but exactly 8 Time
run msg2HonestToIntruder for 3 but exactly 5 Time

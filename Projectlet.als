open util/ordering [Time] as T

sig Time{}
abstract sig LastOperation{}
one sig msg1HonestToIntruder, msg1IntruderToHonest, msg2HonestToIntruder, msg2IntruderToHonest, msg3HonestToIntruder, msg3IntruderToHonest extends LastOperation{}
one sig Track{op: LastOperation lone -> Time}


abstract sig Agent{
	pair: set Agent,
	sharedKey: pair ->  Key
}

sig Honest extends Agent{
	sendMsg1: Nonce  -> Honest -> Time,
	sendMsg2: Enc -> Honest -> Time,
	receivedMsg1: Nonce   ->  Honest ->Time,
	receivedMsg2: Enc -> Honest ->Time,
	to: Agent -> Time,
	from: Agent  -> Time
}

one sig Intruder extends Agent{
	to: Agent set -> Time,
	sendMsg1: Nonce set -> Time,
	sendMsg2: Enc set -> Time,
	receivedMsg1: Nonce set -> Time,
	receivedMsg2: Enc set -> Time,
	from: Agent set -> Time,
	SavedKeys: Key set -> Time
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
	some Intruder.receivedMsg1.t
	some m:Enc | some Intruder.receivedMsg2.t and m in Intruder.receivedMsg2.t and one EncryptKey.t and one Text.t
	some Intruder.SavedKeys.t
	no Intruder.sendMsg1.t
	no Intruder.sendMsg2.t
	no Intruder.to.t
	no Intruder.from.t

}

pred trans[t, t':Time]{
	some  disj a,b:Honest |  some m, m1:Enc | { (msg1HonestToIntruder[t, t', a, b] and Track.op.t'=msg1HonestToIntruder )  
									or (msg1IntruderToHonest[t,t',a,b] and Track.op.t'=msg1IntruderToHonest) 
									or (msg2HonestToIntruder[t,t',a,b, m] and Track.op.t'=msg2HonestToIntruder)
									or (msg2IntruderToHonest[t,t',a,b,m] and Track.op.t'=msg2IntruderToHonest)
									or (msg3HonestToIntruder[t,t',a,b,m1] and Track.op.t'=msg3HonestToIntruder)
									or (msg3IntruderToHonest[t,t',a,b,m1] and Track.op.t'=msg3IntruderToHonest)   
	} 
}

//Operations

pred msg1HonestToIntruder[t,t':Time, Alice,Bob:Honest] {
	
	//Pre conditions 

	//Post Conditions

	let a=Alice.sendMsg1.t , n={ n1:  Nonce | n1 not in a.univ and n1 not in Intruder.receivedMsg1.t  and n1 not in Enc.Text.t}  {   
								 one n
								 Alice.sendMsg1.t'= Alice.sendMsg1.t + (n->Bob)
								 Alice.to.t'= Alice.to.t + Bob
								Intruder.from.t'= Intruder.from.t + Alice
				 				Intruder.receivedMsg1.t'=Intruder.receivedMsg1.t + n  }
	
	//Frame Conditions
	noMessageType1SentExcept[t, t', Alice, none]
	noMessageType2SentExcept[t, t', none, none]
	noMessageType1ReceivedExcept[t, t', none, Intruder]
	noMessageType2ReceivedExcept[t, t', none, none]
	noEncriptedMessageChangeExcept[t, t', none]
	noAgentToChangeExcept[t,t',Alice,none]
	noAgentFromChangeExcept[t,t',none, Intruder]
	noSavedKeyChangesExcept[t,t', none]
}

pred msg1IntruderToHonest[t,t':Time, Alice,Bob:Honest]{

	//Pre Conditions


	some Alice.sendMsg1.t // or some Intruder.receivedMsg1.t 
	some Intruder.receivedMsg1.t // mete por ordem
		


	//Post Conditions
	
	
	let  n = {n1: Nonce | n1 in Intruder.receivedMsg1.t and Bob in Alice.sendMsg1.t [n1] } | { one n   // and mete ordem
												Bob.from.t'=Bob.from.t+Alice
												Intruder.to.t'=Intruder.to.t + Bob
												Bob.receivedMsg1.t'= Bob.receivedMsg1.t + n->Alice 
												Intruder.sendMsg1.t'= Intruder.sendMsg1.t + n   }
	

	

 
	//Frame conditions
	noMessageType1SentExcept[t, t', none, Intruder]
	noMessageType2SentExcept[t, t', none, none]
	noMessageType1ReceivedExcept[t,t', Bob, none]
	noMessageType2ReceivedExcept[t,t',none,none]
	noEncriptedMessageChangeExcept[t,t',none]
	noAgentToChangeExcept[t,t',none, Intruder]
	noAgentFromChangeExcept[t,t',Bob, none]
	noSavedKeyChangesExcept[t,t', none]
}

pred msg2HonestToIntruder[t,t':Time, Alice,Bob:Honest,  m:Enc]{
	//Pre Conditions

		//Alice in Bob.receivedMsg1.t [n]
	//	Alice in Bob.from.t                              old
	//	no Intruder.receivedMsg2.t
	m not in Intruder.receivedMsg2.t and no m.Text.t and no m.Iden.t
	some n:Nonce | Alice in Bob.receivedMsg1.t [n] and Alice in Bob.from.t  
	some n:Nonce |  Bob in Alice.sendMsg1.t [n]
		

	
	//Post Conditions
		
	let  nA={ n: Nonce |  Alice in Bob.receivedMsg1.t[n] } | {
	//	nA->Alice in Bob.receivedMsg1.t
		one nA
		m.EncryptKey.t'= Bob.sharedKey[Alice]  
		m.Text.t'= nA 
		m.Iden.t'= Bob
	
	let nB={ n: Nonce | n != nA  and  n not in (Honest.sendMsg1.t).univ and n not in Enc.Text.t} | {
		one nB
		Bob.to.t'=Bob.to.t + Alice
		Bob.sendMsg1.t'= Bob.sendMsg1.t + nB->Alice
		Bob.sendMsg2.t'=Bob.sendMsg2.t + m->Alice
		Intruder.from.t'=Intruder.from.t + Bob
		Intruder.receivedMsg1.t'=Intruder.receivedMsg1.t + nB
		Intruder.receivedMsg2.t'=Intruder.receivedMsg2.t + m
		Bob.receivedMsg1.t'= Bob.receivedMsg1.t - (nA->Alice)
	}
}	 
		
	//Frame Conditions
		noMessageType1SentExcept[t, t', Bob, none]
		noMessageType2SentExcept[t, t', Bob, none]
		noMessageType2ReceivedExcept[t,t',none, Intruder]
		noMessageType1ReceivedExcept[t,t', Bob, Intruder]
		noEncriptedMessageChangeExcept[t,t',m]
		noAgentToChangeExcept[t,t',Bob,none]
		noAgentFromChangeExcept[t,t',none, Intruder]
		noSavedKeyChangesExcept[t,t', none]
}

pred msg2IntruderToHonest[t, t': Time, Alice,Bob: Honest, e: Enc] {
	
	// Pre Conditions

	// Bob in Intruder.receivedMsg1.t [n]
   	// e in Intruder.receivedMsg2.t              old
	// Alice not in Intruder.sendMsg1.t[n]
	// Alice not in Intruder.to.t
	some Intruder.receivedMsg2.t
	some Intruder.receivedMsg1.t
	some disj nA, nB:Nonce | Bob in Alice.sendMsg1.t [nA] and Alice in Bob.sendMsg1.t [nB] and  Alice in Bob.sendMsg2.t[e] // or e in Intruder.sendMsg2.t myb 
	

		
	
	// Post Conditions

	let send=Alice.sendMsg1.t, nA={ disj n: Nonce | one n and n in send.univ and n->Bob in send}, nB={disj n: Nonce | one n and n != nA 
																			       and n not in send.univ and n in Intruder.receivedMsg1.t} | {
		

			nA=e.Text.t implies {
				Intruder.sendMsg1.t' = Intruder.sendMsg1.t + nB
				Intruder.sendMsg2.t' = Intruder.sendMsg2.t + e
				Intruder.to.t' = Intruder.to.t + Alice		
				Alice.from.t' = Alice.from.t + Bob
				Alice.receivedMsg1.t' = Alice.receivedMsg1.t + nB->Bob
				Alice.receivedMsg2.t' = Alice.receivedMsg2.t + e->Bob
		}
}

	// Frame
	noMessageType1SentExcept[t, t', none, Intruder]
	noMessageType2SentExcept[t, t', none, Intruder]
	noMessageType1ReceivedExcept[t, t', Alice, none]
	noMessageType2ReceivedExcept[t,t', Alice, none]
	noEncriptedMessageChangeExcept[t,t', e]
	noAgentToChangeExcept[t,t',none, Intruder]
	noAgentFromChangeExcept[t,t',Alice, none]
	noSavedKeyChangesExcept[t,t', none]
}

pred msg3HonestToIntruder[t, t': Time, Alice, Bob: Honest,  m: Enc]{

	//PreConditions

	
	some n:Nonce |  Bob in Alice.receivedMsg1.t [n] //and Bob in Alice.receivedMsg2.t [m]  
	m not in Intruder.receivedMsg2.t and m != (Bob.sendMsg2.t).univ and no m.Text.t and no m.Iden.t
	
	//PostConditions
	let receive=Alice.receivedMsg1.t, nB={n: Nonce | one n and n in receive.univ and Bob=Alice.receivedMsg1.t[n]} | {
		m.EncryptKey.t'= Alice.sharedKey[Bob]  
		m.Text.t'=  nB
		m.Iden.t'= Alice
		Alice.sendMsg2.t'=Alice.sendMsg2.t+m->Bob
		Alice.to.t'=Alice.to.t + Bob
	//	Alice.receivedMsg1.t' = Alice.receivedMsg1.t - (nB -> Bob)
		Intruder.from.t'=Intruder.from.t + Alice
		Intruder.receivedMsg2.t'=Intruder.receivedMsg2.t + m
	}

	//Frame
	noMessageType1SentExcept[t, t', none, none]
	noMessageType2SentExcept[t, t', Alice, none]
	noMessageType1ReceivedExcept[t, t', none,  none]
	noMessageType2ReceivedExcept[t,t',none, Intruder]
	noEncriptedMessageChangeExcept[t,t',m]
	noAgentToChangeExcept[t,t',Alice,none]
	noAgentFromChangeExcept[t,t',none, Intruder]
	noSavedKeyChangesExcept[t,t', none]

}

pred msg3IntruderToHonest[t, t': Time, Alice, Bob: Honest, e: Enc] {
	
	// Pre Conditions

	some Intruder.receivedMsg2.t
	e in Intruder.receivedMsg2.t


	// Post Conditions

	let send=Bob.sendMsg1.t, nB={ n: Nonce | one n and n in send.univ and n->Alice in send} | {


		nB=e.Text.t implies {
		Intruder.sendMsg2.t' = Intruder.sendMsg2.t + e
		Intruder.to.t' = Intruder.to.t + Bob
		Bob.from.t' = Bob.from.t + Alice
		Bob.receivedMsg2.t' = Bob.receivedMsg2.t + e->Alice
		}
	}
	// Frame
	noMessageType1SentExcept[t, t', none, none]
	noMessageType2SentExcept[t, t', none, Intruder ]
	noMessageType1ReceivedExcept[t, t', none,  none]
	noMessageType2ReceivedExcept[t,t',Bob, none]
	noEncriptedMessageChangeExcept[t,t',none]
	noAgentToChangeExcept[t,t',none, Intruder]
	noAgentFromChangeExcept[t,t',Bob, none]
	noSavedKeyChangesExcept[t,t', none]
}


//Frame Conditions

pred noMessageType1SentExcept[t,t':Time, a: set Honest, i:Intruder]{
	all h:Honest - a | h.sendMsg1.t'=h.sendMsg1.t
	(i=none) implies Intruder.sendMsg1.t'=Intruder.sendMsg1.t 
}

pred noMessageType2SentExcept[t,t':Time, a: set Honest, i:Intruder]{
	all h:Honest - a |   h.sendMsg2.t'=h.sendMsg2.t 
	(i=none) implies  Intruder.sendMsg2.t'=Intruder.sendMsg2.t
}

pred noMessageType1ReceivedExcept[t,t':Time, a: set Honest, i:Intruder]{
	all h:Honest - a | h.receivedMsg1.t'=h.receivedMsg1.t 
	(i=none) implies Intruder.receivedMsg1.t'=Intruder.receivedMsg1.t 
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

pred noSavedKeyChangesExcept[t,t':Time, k:set Key]{
	 Intruder.SavedKeys.t'=Intruder.SavedKeys.t 
}

//Facts

pred AgentFacts{
	all a:Agent | (Agent-a) in a.pair and a not in a.pair
	all a,b: Agent | a in b.pair implies ( b in a.pair and one a.sharedKey[b] and one b.sharedKey[a] and a.sharedKey[b] = b.sharedKey[a])
//	all a,b,c: Agent, k:Key | b->k in a.sharedKey and c->k in a.sharedKey implies b=c
//	all  disj a,b,c: Agent |   (a.sharedKey[b] != a.sharedKey[c]) 	
	all  disj a, b,c: Agent | let s= (Agent-a-b).sharedKey | a.sharedKey[b] != a.sharedKey[c]  and a.sharedKey[b] not in univ.s
}


fact{
	init [T/first]
	all t: Time - T/last | trans [t, T/next[t]]
	all t: Time | all h:Honest | Intruder not in h.from.t and Intruder not in h.to.t 
	all t: Time | all h:Honest | h not in h.to.t and h not in h.from.t and Intruder not in Intruder.from.t and Intruder not in Intruder.to.t
	AgentFacts
}

pred Sequence {
	some disj t0,t1,t2,t3,t4,t5,t6: Time | some disj a,b:Honest | some disj m, m1:Enc |  { t0=T/first and t1=t0.next and t2=t1.next and t3=t2.next and t4=t3.next and t5=t4.next and t6=t5.next
													and(msg1HonestToIntruder[t0, t1, a, b] and Track.op.t1=msg1HonestToIntruder )  
													and (msg1IntruderToHonest[t1,t2,a,b] and Track.op.t2=msg1IntruderToHonest) 
													and (msg2HonestToIntruder[t2,t3,a,b, m] and Track.op.t3=msg2HonestToIntruder)
													and (msg2IntruderToHonest[t3,t4,a,b,m] and Track.op.t4=msg2IntruderToHonest)
													and (msg3HonestToIntruder[t4,t5,a,b,m1] and Track.op.t5=msg3HonestToIntruder)
													and (msg3IntruderToHonest[t5,t6,a,b,m1] and Track.op.t6=msg3IntruderToHonest)   
	} 
}

// If Alice received nB, {nA} * kAB then
// Bob has sent before {nA} * kAB to Intruder


// 10
pred AliceAuthenticatesBob[disj Alice, Bob: Honest, e: Enc] {
	
	// t =>  msg2IntruderToHonest 		Time when alice received nonce and {nA} * kAB from Intruder ("Bob") 
	// t.prev => msg2HonestToIntruder		Time when bob sent
	// t.prev.prev => msg1.IntruderToHonest  Time when bob received nA

	some t: Time | let e = Alice.receivedMsg2.t.Bob {
		Bob.receivedMsg1[e.Text.(t.prev)].(t.prev.prev) = Alice and Alice.sharedKey.(e.EncryptKey.(t.prev)) = Bob implies {
			Bob.sendMsg2.(t.prev).Alice = e
		}
	}
}

// 10
assert AliceAuthsBob {
	all disj a, b: Honest, e: Enc | AliceAuthenticatesBob[a,b,e]
}

//Runs

run msg1HonestToIntruder for 3 but exactly 8 Time
run msg1IntruderToHonest for 3 but exactly 8 Time
run msg2HonestToIntruder for 3 but exactly 8 Time
run msg2IntruderToHonest for 3 but exactly 8 Time
run msg3HonestToIntruder for 3 but exactly 8 Time
run msg3IntruderToHonest for 3 but exactly 8 Time
run Sequence for 7 but 3 Agent

check canDoProtocol for 3 but exactly 8 Time
check AliceAuthsBob for 3

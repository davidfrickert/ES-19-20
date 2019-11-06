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
	//7 Set of saved keys
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
	no Intruder.sendMsg1.t
	no Intruder.sendMsg2.t
	no Intruder.to.t
	no Intruder.from.t

	//7 Initially the intruder knows some nonces, keys and encrypted messages
	some Intruder.receivedMsg1.t
	some m:Enc | some Intruder.receivedMsg2.t and m in Intruder.receivedMsg2.t and one EncryptKey.t and one Text.t
	some Intruder.SavedKeys.t
	
}

pred trans[t, t':Time]{
	some disj a,b :Honest |  some disj nA, nB:Nonce, m:Enc | { (msg1HonestToIntruder[t, t', a, b, nA] and Track.op.t'=msg1HonestToIntruder )  
								or (msg1IntruderToHonest[t,t',a,b, nA] and Track.op.t'=msg1IntruderToHonest) 
								or (msg2HonestToIntruder[t,t',a,b, nB, m] and Track.op.t'=msg2HonestToIntruder)
								or (msg2IntruderToHonest[t,t',a,b,m, nB] and Track.op.t'=msg2IntruderToHonest)
								or (msg3HonestToIntruder[t,t',a,b,m] and Track.op.t'=msg3HonestToIntruder)
								or (msg3IntruderToHonest[t,t',a,b,m] and Track.op.t'=msg3IntruderToHonest)   
	} 
}

pred msg1HonestToIntruder[t,t':Time, Alice,Bob:Honest, n1:Nonce] {
	
	//Pre conditions 
	
	//Fresh Nonce
	n1 not in (Honest.sendMsg1.t).univ and n1 not in Intruder.receivedMsg1.t and n1 not in Enc.Text.t

	//1  No Pre Conditions for Agents only requires a fresh nonce
	//5 No Pre Conditions for Intruders to receive a message
 

	//Post Conditions
					 
	Alice.sendMsg1.t'= Alice.sendMsg1.t + (n1->Bob)
	Alice.to.t'= Alice.to.t + Bob
	Intruder.from.t'= Intruder.from.t + Alice
	Intruder.receivedMsg1.t'=Intruder.receivedMsg1.t + n1 

	//8 Encrypt ?
//	let m={ m1: Enc  | one m1 and m1 not in (Honest.sendMsg2.t).univ } | Alice.sharedKey[Bob] in Intruder.SavedKeys.t' implies  m.EncryptKey.t'= Alice.sharedKey[Bob] and m.Text.t'=n1 and Intruder.sendMsg2.t'=Intruder.sendMsg2.t + m
	
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

pred msg1IntruderToHonest[t,t':Time, Alice,Bob:Honest, n:Nonce]{

	//Pre Conditions

	//Implicit Intruder pretends to be Alice or forwards message
	n in Intruder.receivedMsg1.t or n in Alice.sendMsg1.t.Bob
	
	//2 No Pre condition for Honest to receive
	
	//6 Always ready to send a message because it has saved messages in the beginning or received earlier
	some Intruder.receivedMsg1.t

	//Post Conditions

	Bob.from.t'=Bob.from.t+Alice
	Intruder.to.t'=Intruder.to.t + Bob
	Bob.receivedMsg1.t'= Bob.receivedMsg1.t + n->Alice 
	Intruder.sendMsg1.t'= Intruder.sendMsg1.t + n   
	
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

pred msg2HonestToIntruder[t,t':Time, Alice,Bob:Honest, nB:Nonce, m:Enc]{

	//Pre Conditions
	
	//Fresh nonce and Enc for Bob to send to Alice
	m not in (Honest.sendMsg2.t).univ and m not in Intruder.receivedMsg2.t and no m.Text.t and no m.Iden.t and no m.EncryptKey.t
	nB not in (Honest.sendMsg1.t).univ and nB not in Intruder.receivedMsg1.t and nB not in Enc.Text.t 

	//3 Requires a nonce to be received from Alice to continue protocol
	some n:Nonce | Alice in Bob.receivedMsg1.t [n] and Alice in Bob.from.t  

	//5 No Pre Conditions for Intruder to receive a message
	
	
	let  nA={ n: Nonce |  Alice in Bob.receivedMsg1.t[n] } | {	
		one nA

	//Post Conditions

		m.EncryptKey.t'= Bob.sharedKey[Alice]  
		m.Text.t'= nA 
		m.Iden.t'= Bob                 //Fix
	
		Bob.to.t'=Bob.to.t + Alice
		Bob.sendMsg1.t'= Bob.sendMsg1.t + nB->Alice
		Bob.sendMsg2.t'=Bob.sendMsg2.t + m->Alice
		Bob.receivedMsg1.t'= Bob.receivedMsg1.t - (nA->Alice)		

		Intruder.from.t'=Intruder.from.t + Bob
		Intruder.receivedMsg1.t'=Intruder.receivedMsg1.t + nB
		Intruder.receivedMsg2.t'=Intruder.receivedMsg2.t + m
		//8 ?
		m.EncryptKey.t' in Intruder.SavedKeys.t implies Intruder.receivedMsg1.t'=Intruder.receivedMsg1.t' + m.Text.t' 
	
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

pred msg2IntruderToHonest[t, t': Time, Alice,Bob: Honest, e: Enc, nB:Nonce] {
	
	// Pre Conditions

	//6 Always ready to send a message because it has saved messages in the beginning or received earlier
	some Intruder.receivedMsg2.t  //4  Provides that earlier exchanges happened
	some Intruder.receivedMsg1.t   //4  Provides that earlier exchanges happened

	//4 Provides that earlier exchanges happened
	some disj nA, nB:Nonce | Bob in Alice.sendMsg1.t [nA] and Alice in Bob.sendMsg1.t [nB] and  Alice in Bob.sendMsg2.t[e] //4

	//Implicit pretends to be Bob or forwards message
	nB in Intruder.receivedMsg1.t or nB->Alice in Bob.sendMsg1.t

	

	e.Iden.t=Bob	//Fix
	
	

	let send=Alice.sendMsg1.t, nA={ disj n: Nonce | one n and n in send.univ and n->Bob in send} | {
			
	//8 Intruder can decrypt Enc and save the nonce
	e in Intruder.receivedMsg2.t or (e.EncryptKey.t in Intruder.SavedKeys.t and e.Text.t in Intruder.receivedMsg1.t )
			nA in e.Text.t and e.EncryptKey.t in Alice.sharedKey[Bob] implies {

	// Post Conditions
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
	noEncriptedMessageChangeExcept[t,t', none]
	noAgentToChangeExcept[t,t',none, Intruder]
	noAgentFromChangeExcept[t,t',Alice, none]
	noSavedKeyChangesExcept[t,t', none]
}

pred msg3HonestToIntruder[t, t': Time, Alice, Bob: Honest, m: Enc]{

	//PreConditions

	//Fresh Enc
	m not in (Honest.sendMsg2.t).univ and m not in Intruder.receivedMsg2.t  and no m.Text.t and no m.Iden.t and no m.EncryptKey.t

	//3 Ready to continue if it has a nonce and Enc from Bob
	some n:Nonce |  Bob in Alice.receivedMsg1.t [n] 
	some e:Enc | e!=m and Bob in Alice.receivedMsg2.t [e] 
	
	//5 No Pre condition for Intruder to receive a message
	
	let  nB={n: Nonce | Bob in Alice.receivedMsg1.t[n] and (n->Bob) in Alice.receivedMsg1.t } | {

	//PostConditions	
		m.EncryptKey.t'= Alice.sharedKey[Bob]  
		m.Text.t'= nB
		m.Iden.t'= Alice      //Fix
		Alice.sendMsg2.t'=Alice.sendMsg2.t + m->Bob
		Alice.to.t'=Alice.to.t + Bob
		Alice.receivedMsg1.t' = Alice.receivedMsg1.t - (nB->Bob)
		Intruder.from.t'=Intruder.from.t + Alice
		Intruder.receivedMsg2.t'=Intruder.receivedMsg2.t + m

			//8
		m.EncryptKey.t' in Intruder.SavedKeys.t implies Intruder.receivedMsg1.t'=Intruder.receivedMsg1.t' + m.Text.t'
	}

	//Frame Conditions
	noMessageType1SentExcept[t, t', none, none]
	noMessageType2SentExcept[t, t', Alice, none]
	noMessageType1ReceivedExcept[t, t', Alice,  none]
	noMessageType2ReceivedExcept[t,t',none, Intruder]
	noEncriptedMessageChangeExcept[t,t',m]
	noAgentToChangeExcept[t,t',Alice,none]
	noAgentFromChangeExcept[t,t',none, Intruder]
	noSavedKeyChangesExcept[t,t', none]

}

pred msg3IntruderToHonest[t, t': Time, Alice, Bob: Honest, e: Enc] {
	
	// Pre Conditions
	
	//4 Provides that earlier exchange happened
	some disj m, m1:Enc | m1 = e and m!=e and Bob in Alice.receivedMsg2.t [m] and m1 in Alice.sendMsg2.t.univ 

	//6 Always ready to send a message because it has saved messages in the beginning or received earlier
	some Intruder.receivedMsg2.t 	

	//Implicitly pretends to be Bob or forwards message
	e in Intruder.receivedMsg2.t or Bob in Alice.sendMsg2.t[e] 
	
	

	e.Iden.t=Alice     //Fix

	

	let send=Bob.sendMsg1.t, nB={ n: Nonce | one n and n in send.univ and n->Alice in send} | {

		//8 Intruder can decript Enc and save the nonce
		e in Intruder.receivedMsg2.t or (e.EncryptKey.t in Intruder.SavedKeys.t and e.Text.t in Intruder.receivedMsg1.t )
		nB=e.Text.t and e.EncryptKey.t in Bob.sharedKey[Alice] implies {

	// Post Conditions
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

fact{
	init [T/first]
	all t: Time - T/last | trans [t, T/next[t]]
	all t: Time | all h:Honest | Intruder not in h.from.t and Intruder not in h.to.t 
	all t: Time | all h:Honest | h not in h.to.t and h not in h.from.t and Intruder not in Intruder.from.t and Intruder not in Intruder.to.t
	all a:Agent | (Agent-a) in a.pair and a not in a.pair
	all a,b: Agent | a in b.pair implies ( b in a.pair and one a.sharedKey[b] and one b.sharedKey[a] and a.sharedKey[b] = b.sharedKey[a])	
	all  disj a, b,c: Agent | let s= (Agent-a-b).sharedKey | a.sharedKey[b] != a.sharedKey[c]  and a.sharedKey[b] not in univ.s
}

//10
pred Sequence {
	some disj t0,t1,t2,t3,t4,t5,t6: Time | some disj a,b:Honest | some disj nA,nB:Nonce, disj m,m1:Enc | { t0=T/first and t1=t0.next and t2=t1.next and t3=t2.next and t4=t3.next and t5=t4.next and t6=t5.next
													and(msg1HonestToIntruder[t0, t1, a, b, nA] and Track.op.t1=msg1HonestToIntruder )  
													and (msg1IntruderToHonest[t1,t2,a,b, nA] and Track.op.t2=msg1IntruderToHonest) 
													and (msg2HonestToIntruder[t2,t3,a,b, nB, m] and Track.op.t3=msg2HonestToIntruder)
													and (msg2IntruderToHonest[t3,t4,a,b,m, nB] and Track.op.t4=msg2IntruderToHonest)
													and (msg3HonestToIntruder[t4,t5,a,b,m1] and Track.op.t5=msg3HonestToIntruder)
													and (msg3IntruderToHonest[t5,t6,a,b,m1] and Track.op.t6=msg3IntruderToHonest)   
	} 
}


// If Alice received nB, {nA} * kAB then
// Bob has sent before {nA} * kAB to Intruder


// 11
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

// 11
assert AliceAuthsBob {
	all disj a, b: Honest, e: Enc | AliceAuthenticatesBob[a,b,e]
}

//12 
assert BobAuthsAlice{
	some t1, t2: Time, m:Enc , disj Alice, Bob:Honest | { t2=t1.next
	     and (Alice in Bob.receivedMsg2.t2 [m] and m.EncryptKey.t2= Alice.sharedKey[Bob] and m.Text.t2 = Bob.sendMsg1.t2.Alice implies Bob in (Alice.sendMsg2).t1 [m] ) }
}

//13 
assert ProtocolInit{
	
}
//Runs

run msg1HonestToIntruder for 3 but exactly 8 Time
run msg1IntruderToHonest for 3 but exactly 8 Time
run msg2HonestToIntruder for 3 but exactly 8 Time
run msg2IntruderToHonest for 3 but exactly 8 Time
run msg3HonestToIntruder for 3 but exactly 8 Time
run msg3IntruderToHonest for 3 but exactly 8 Time
run Sequence for 7 but 3 Agent

check AliceAuthsBob for 3
check BobAuthsAlice for 3

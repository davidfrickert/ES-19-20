open util/ordering [Time] as T

sig Time{}

abstract sig Agent{
	pair:set Agent
	symKey: pair lone -> Key
}{
	all a:Agent | a not in pair
}
sig Honest extends Agent{
	sendMsg1: Nonce  -> Honest -> Time,
	sendMsg2: Nonce  -> Honest -> Time,
//	received: Nonce set -> Time,
	receivedMsg1: Nonce -> Honest ->Time,
	receivedMsg2: Nonce -> Honest ->Time,
	to: Agent lone -> Time,
	from: Agent lone -> Time
}

one sig Intruder extends Agent{
	to: Agent lone -> Time,
//	received: Nonce set -> Time,
	received: Nonce -> Honest ->Time,
	from: Agent lone -> Time
}

sig Key{}
sig Nonce{}
/*
sig Enc{
	key: one Key
}*/

pred init [t: Time]{
	no Honest.receivedMsg1.t
	no  Honest.sendMsg1.t
	no  Honest.to.t
	no  Honest.from.t
	no Intruder.received.t
	no  Intruder.to.t
	no  Intruder.from.t
}

pred trans[t, t':Time]{
	some a,b:Honest | let n= Nonce | SendMsg1[t, t', a, b, n] 
}

pred SendMsg1[t,t':Time, Alice,Bob:Honest, n:Nonce] {
	
	//Pre conditions 

	//Post Conditions
	Alice.to.t'= Alice.to.t + Bob
	Alice.sendMsg1.t'=Alice.sendMsg1.t + n->Bob
	Intruder.received.t'=Intruder.received.t + n->Alice
	Intruder.from.t'= Intruder.from.t + Alice
	Intruder.to.t'=Intruder.to.t + Bob
	//Frame Conditions

}



fact{
	init [T/first]
	all t: Time - T/last | trans [t, T/next[t]]
	all t: Time | all h:Honest | Intruder not in h.from.t and Intruder not in h.to.t 
	all t: Time | all h:Honest | h not in h.to.t and h not in h.from.t
}






run SendMsg1 for 5

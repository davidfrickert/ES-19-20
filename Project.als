open util/ordering [Time] as T

sig Time{}

abstract sig Agent{
	pair: lone Agent
}{
	all a:Agent | a not in pair
}
sig Honest extends Agent{
	send: Nonce set -> Time,
	received: Nonce set -> Time,
	to: Agent lone -> Time,
	from: Agent lone -> Time
}{
//	all t: Time| all h:Honest | h not in to.t and h not in from.t
	
}
one sig Intruder extends Agent{
	to: Agent lone -> Time,
	received: Nonce set -> Time,
	from: Agent lone -> Time
}{
//	all t: Time| Intruder not in to.t and Intruder not in from.t
}

//sig Key{}
sig Nonce{}
/*
sig Enc{
	key: one Key
}*/

pred init [t: Time]{
	no Honest.received.t
	no  Honest.send.t
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
	//Bob in Alice.to.t and n in Alice.send and n in Intruder.received and Alice in Intruder.from and n in Intruder.received and Bob in Intruder.to 
	//	all h:Honest | one h.from and one h.to
	Alice.to.t'= Alice.to.t + Bob
	Alice.send.t'=Alice.send.t + n
	Intruder.received.t'=Intruder.received.t + n
	Intruder.from.t'= Intruder.from.t + Alice
	Intruder.to.t'=Intruder.to.t + Bob
	n not in Bob.received.t'
	n not in Alice.received.t'
}



fact{
	init [T/first]
	all t: Time - T/last | trans [t, T/next[t]]
	all t: Time | all h:Honest | Intruder not in h.from.t and Intruder not in h.to.t 
}






run SendMsg1 for 5

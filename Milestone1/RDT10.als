module RDT10

open util/ordering[State]

sig Data {}

sig Packet {
//	dataSlice: one Data
}

sig Receiver{
	data: set Packet
}

sig Sender{
	receiver: one Receiver,
	data: set Packet
}

sig State{
	currentSender: one Sender,
	buffer: lone Packet
}

pred sendPacket[s, s': State] {
//	s.currentSender in Sender - s'.currentSender and
/*	one p: Packet | p = s'.packetSent and
	(one d:Packet|//Data |
		//Starts in sender buffer
		d in s.currentSender and
		//Does not exist in the sender buffer in next state
		d not in s'.currentSender and
		//Does not start in receiver buffer
		d not in s.currentReceiver and
		//Does not end in receiver buffer
		d not in s'.currentReceiver and
		//Goes to packetSent
		d = s'.packetSent and//.dataSlice and
	//All other data in sender/receiver buffer does not change
		s'.currentSender - d = s.currentSender - d and
		s'.currentReceiver - d = s.currentReceiver - d)*/


	s.buffer = none and
	one p:Packet | p in data[s.currentSender] and p in s'.buffer and p !in data[s'.currentSender]
		and p !in data[s'.currentSender.receiver]  and (data[s'.currentSender.receiver] = data[s.currentSender.receiver])
		and (data[s'.currentSender] = data[s.currentSender] - p)
}

pred receivePacket[s, s': State] {
//	s.currentSender = s'.currentSender and
//	s.currentReceiver in Receiver - s'.currentReceiver and
/*	one p: Packet | p = s.packetSent and
	s'.packetSent = none
	(one d:Packet|//Data |
		//Starts in packetSent
		d = s.packetSent and //.dataSlice and
		//Does not start in sender buffer
		d not in s.currentSender and
		//Does not finish in sender buffer
		d not in s'.currentSender and
		//Does not start in receiver buffer
		d not in s.currentReceiver and
		//Finishes in receiver buffer
		d in s'.currentReceiver and
	//All other data in sender/receiver buffer does not change
		s'.currentSender - d = s.currentSender - d and
		s'.currentReceiver - d = s.currentReceiver - d)*/
}

fact{
	all s:Sender | (all s2:Sender - s | s.receiver != s2.receiver and
		(no p:Packet | p in s.data and p in s2.data or (p in s.receiver.data and p in s2.receiver.data))) and
	(all p:Packet | no s,s2:Sender | p in s.data and p in s2.receiver.data) and
	no r:Receiver | all s:Sender | r !in s.receiver
}

pred Transition[s, s':State]{
	sendPacket[s, s']// or receivePacket[s, s']
}

pred State.Init[]{
	all r:
}

pred show{}

run show for 4

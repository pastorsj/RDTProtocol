module RDT10

sig Data {}

sig Packet {
	dataSlice: one Data
}

sig Sender {
	buffer: set Data
}

sig Receiver {
	buffer: set Data
}

sig State{
	currentReceiver: one Receiver,
	currentSender: one Sender,
	packetSent: lone Packet
}

pred sendPacket[s, s': State] {
//	s.currentReceiver = s'.currentReceiver and
//	s.currentSender in Sender - s'.currentSender and
	s.packetSent = none and
	one p: Packet | p = s'.packetSent and
	(one d:Data |
		//Starts in sender buffer
		d in s.currentSender.buffer and
		//Does not exist in the sender buffer in next state
		d not in s'.currentSender.buffer and
		//Does not start in receiver buffer
		d not in s.currentReceiver.buffer and
		//Does not end in receiver buffer
		d not in s'.currentReceiver.buffer and
		//Goes to packetSent
		d = s'.packetSent.dataSlice and
	//All other data in sender/receiver buffer does not change
		
}

pred receivePacket[s, s': State] {
//	s.currentSender = s'.currentSender and
//	s.currentReceiver in Receiver - s'.currentReceiver and
	one p: Packet | p = s.packetSent and
	s'.packetSent = none
	(one d:Data |
		//Starts in packetSent
		d = s.packetSent.dataSlice and
		//Does not start in sender buffer
		d not in s.currentSender.buffer and
		//Does not finish in sender buffer
		d not in s'.currentSender.buffer and
		//Does not start in receiver buffer
		d not in s.currentReceiver.buffer and
		//Finishes in receiver buffer
		d in s'.currentReceiver.buffer and
	//All other data in sender/receiver buffer does not change
}

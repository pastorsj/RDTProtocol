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
	currentPacket: lone Packet
}

pred sendPacket[s, s': State] {

}

pred receivePacket[s, s': State] {

}

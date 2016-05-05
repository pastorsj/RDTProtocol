module Milestone2/RDT20

open util/ordering[State]

one sig ACK, NAK extends Packet{}

sig Checksum{}

one sig CorruptChecksum extends Checksum{}

sig Data{}

sig Packet{ 
	data: Data,
	checksum : Checksum
}

sig Receiver{
	sender: one Sender
}

sig Sender{
	receiver: one Receiver
}

sig State{
	senders: (Sender -> Packet),
	receivers: (Receiver -> Packet),
	buffer: (Sender -> Packet),
	lastPacket: (Sender -> Packet),
	replyBuffer: (Receiver -> Packet),
	replies: (Sender -> Packet)
}



pred SendPacket[s,s':State]{
	(one send:Sender |
		(s.buffer[send] = none) and
		(one p:(Packet - (ACK + NAK)) |
			(let sendPair = (send->p) |
				((((send->NAK) in s.replies) => (sendPair in s.lastPacket)) and
				(((send->ACK) in s.replies) => (sendPair in s.senders)) and
				#s.replyBuffer = 0 and
				sendPair !in s'.senders and
				sendPair in s'.buffer and
				sendPair in s'.lastPacket and
				#s.buffer = 0 and
				s'.senders = s.senders - sendPair and
				s.receivers = s'.receivers and
				s'.lastPacket = (s.lastPacket) - (send->s.lastPacket[send]) + sendPair and
				s.replies = s'.replies and
				s.replyBuffer = s'.replyBuffer and
				s.buffer = s'.buffer - sendPair))))
}

pred ReceivePacket[s,s':State]{
	(one send:Sender | 
		(one p: Packet|
			(one r: Receiver|
				(#s.replyBuffer = 0) and
				(p.ErrorCheck[] => s'.replyBuffer = (r->ACK)) and
				(!p.ErrorCheck[] => s'.replyBuffer = (r->NAK)) and
				(#s'.buffer = 0) and
				((s.buffer[send] = p) and
				(send.receiver = r) and
				(let sendPair = (send->p) |
					(let receivePair = (r -> p)|
						(s'.buffer = s.buffer - sendPair and
						(p.ErrorCheck[] => receivePair in s'.receivers) and
						receivePair !in s.receivers and
						s.lastPacket = s'.lastPacket and
						s'.receivers - receivePair = s.receivers and
						s.replies = s'.replies and
						s.senders = s'.senders)))))))
}

pred ReceiveReply[s,s':State]{
	(one r:Receiver|
		(one p:(ACK + NAK)|
			(one send:Sender|
				send = r.sender and
				s'.replies = (s.replies - (send->s.replies[send]))+ (send->p) and
				s.lastPacket = s'.lastPacket and
				s.receivers = s'.receivers and
				s.buffer = s'.buffer and
				s.senders = s'.senders and
				(r->p) in s.replyBuffer and
				s'.replyBuffer = s.replyBuffer - (r->p))))
}

pred Packet.ErrorCheck{
	this.checksum != CorruptChecksum
}

pred State.Done[]{
	#this.senders = 0 and #this.buffer = 0 and #this.replyBuffer = 0
}

pred State.Init[]{
	#this.receivers = 0 and #this.buffer = 0  and #this.replyBuffer = 0 and #this.lastPacket = 0 and this.replies = {Sender->ACK}
	and all s:Sender | (s->ACK) !in this.senders and (s->NAK) !in this.senders
}

pred Transition[s, s':State]{
	SendPacket[s, s'] or 
	ReceivePacket[s, s'] or ReceiveReply[s, s']
}

fact{
	receiver = ~sender
}

fact{
	some p:Sender.(first.senders) | p.checksum = CorruptChecksum
}

fact{
	(no p:Packet | (some r:Receiver | (some r2:Receiver - r | (r->p) in State.receivers and (r2->p) in State.receivers))
		or (some s:Sender| (some s2:Sender -s | ((s->p) in State.senders and (s2->p) in State.senders)
			or ((s->p) in State.buffer and (s2->p) in State.buffer)
			or ((s->p) in State.lastPacket and (s2->p) in State.lastPacket))))
}

fact{
	(all st:State | no p:Packet | (p in Sender.(st.senders) and p in Receiver.(st.receivers))
		or (p in Sender.(st.senders) and p in Sender.(st.buffer))
		or (p in Sender.(st.buffer) and p in Receiver.(st.receivers))) 
}

assert AlwaysWorks{
	(first.Init[]  and
		all s:State - last |
			let s' = s.next |
				Transition[s, s'] )=> last.Done[]
}

pred Trace[]{
	first.Init[] and
		all s:State - last |
			let s' = s.next |
				Transition[s, s']
}

pred show{}
check AlwaysWorks for 2 but exactly 5 State
run Trace for 2 but exactly 9 State, exactly 4 Packet
run show for 2 but exactly 5 State

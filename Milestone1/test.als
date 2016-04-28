
open util/ordering[State]

sig Packet{}
sig Receiver{}
sig Sender{
	receiver: one Receiver
}
sig State{
	senders: (Sender -> Packet),
	receivers: (Receiver -> Packet),
	buffer: (Sender -> Packet)
}
pred SendPacket[s,s':State]{
	(one sender:Sender |
		(s.buffer[sender] = none) and
		(one p:Packet |
			(let sendPair = (sender->p) |
				(sendPair in s.senders and
				sendPair !in s'.senders and
				sendPair in s'.buffer and
				sendPair !in s.buffer and
				s'.senders = s.senders - sendPair and
				s.receivers = s'.receivers))))
}

fact{
	all s:Sender| lone State.buffer[s]
}

pred ReceivePacket[s,s':State]{
	(one sender:Sender | 
		(one p: Packet|
			(one r: Receiver|
				((s.buffer[sender] = p) and
				(sender.receiver = r) and
				(let sendPair = (sender->p) |
					(let receivePair = (r -> p)|
						(sendPair in s.buffer and
						sendPair !in s'.buffer and
						receivePair in s'.receivers and
						receivePair !in s.receivers and
						s'.receivers = s.receivers - receivePair and
						s.senders = s'.senders)))))))
}

pred State.Init[]{
	Receiver.(this.receivers) = none and
	Sender.(this.buffer) = none
}

pred Transition[s, s':State]{
	SendPacket[s, s'] or 
	ReceivePacket[s, s']
}

fact{
	(no p:Packet | (some r:Receiver | (some r2:Receiver - r | (r->p) in State.receivers and (r2->p) in State.receivers))
		or (some s:Sender| (some s2:Sender -s | (s->p) in State.senders and (s2->p) in State.senders)))
}

fact{
	(all st:State | no p:Packet | (p in Sender.(st.senders) and p in Receiver.(st.receivers))
		or (p in Sender.(st.senders) and p in Sender.(st.buffer))
		or (p in Sender.(st.buffer) and p in Receiver.(st.receivers))) 
}

fact{
	(no s:Sender | some s2:Sender - s | s.receiver = s2.receiver)
}

pred Trace[]{
	first.Init[] and
		all s:State - last |
			let s' = s.next |
				Transition[s, s']
}

pred show{}
run Trace for 6

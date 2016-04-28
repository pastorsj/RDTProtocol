
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
	(one sender:Sender | (one p:Packet | (let sendPair = (sender->p) |
		(sendPair in s.senders and sendPair !in s'.senders and sendPair in s'.buffer
			and s'.senders - sendPair = s.senders - sendPair
			and s.receivers = s'.receivers))))
}

pred State.Init[]{
	Receiver.(this.receivers) = none// and
//	Sender.(this.buffer) = none
}

fact{
	first.Init[] and
	(no p:Packet | (some r:Receiver | (some r2:Receiver - r | (r->p) in State.receivers and (r2->p) in State.receivers))
		or (some s:Sender| (some s2:Sender -s | (s->p) in State.senders and (s2->p) in State.senders))) and
	(all st:State | no p:Packet | (p in Sender.(st.senders) and p in Receiver.(st.receivers))
		or (p in Sender.(st.senders) and p in Sender.(st.buffer))
		or (p in Sender.(st.buffer) and p in Receiver.(st.receivers))) 
	
}

pred show{}
run SendPacket for 2 but exactly 2 Sender

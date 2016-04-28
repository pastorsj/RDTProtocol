module Milestone1/RDT10

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
				s.receivers = s'.receivers and
				s.buffer = s'.buffer - sendPair))))
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
						s'.receivers - receivePair = s.receivers and
						s.senders = s'.senders)))))))
}

pred State.Done[]{
	#this.senders = 0 and #this.buffer = 0
}

pred State.Init[]{
	#this.receivers = 0 and #this.buffer = 0
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
run Trace for 2 but exactly 5 State
run show for 2 but exactly 5 State

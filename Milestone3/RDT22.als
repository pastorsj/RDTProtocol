module Milestone3/RDT22

open util/ordering[State]

one sig ACK extends Data{}

sig Checksum{}

abstract sig SequenceNumber{}

one sig Seq0, Seq1 extends SequenceNumber{}

one sig CorruptChecksum extends Checksum{}

sig Data{}

sig Packet{ 
	data : one Data,
	checksum : one Checksum,
	seqNum : one SequenceNumber
}

sig Receiver{
	sender: one Sender
}

sig Sender{
	receiver: one Receiver
}

sig State{
	type: one StateType,
	sent: set Packet,
	senders: (Sender -> Data),
	receivers: (Receiver -> Data),
	buffer: (Sender -> Packet),
	lastSent: (Sender -> Data),
	lastPacket: (Sender -> Packet),
	lastSentNum: (Sender -> SequenceNumber),
	replyNum: (Sender -> SequenceNumber),
	lastReceivedNum: (Receiver -> SequenceNumber),
	replyBuffer: (Receiver -> Packet),
	replies: (Sender -> Data)
}

abstract sig StateType{}

one sig SendState, ReceiveState, ReceiveReplyState, DeadState extends StateType{}



pred ReSendPacket[s,s':State]{
	s.type = DeadState and
	(one send:Sender |
		(s.buffer[send] = none) and
		(let p = s.lastPacket[send] |
			(let sendPair = (send->p) |
				s.sent = s'.sent and
				s.senders = s'.senders and
				s.receivers = s'. receivers and
				s.lastSent = s'.lastSent and
				s.lastSentNum = s'.lastSentNum and
				s.lastReceivedNum = s'.lastReceivedNum and
				s.lastPacket = s'.lastPacket and
				#s.replyBuffer = 0 and
				s.replies = s'.replies and
				s.replyNum = s'.replyNum and
				s'.buffer = sendPair)))
}

pred CanSendPacket[s:State]{
	(one send:Sender |
		(some d:(Data - (ACK)) |			
			(some p:(Packet - s.sent) | d = p.data) and
			(let sendData = (send -> d) |
				((s.replyNum[send] != s.lastSentNum[send])=> (sendData in s.lastSent)) and
				((s.replyNum[send] = s.lastSentNum[send]) => (sendData in s.senders)) and
				#s.replyBuffer = 0 and
				#s.buffer = 0)))
}

pred SendPacket[s,s':State]{
	s.type = SendState and
	CanSendPacket[s] and
	(one send:Sender |
		(s.buffer[send] = none) and
		(one p:(Packet - s.sent) |
			p in s'.sent and
			p.seqNum = SequenceNumber - send.(s.lastSentNum) and
			(one d:(Data - (ACK)) |
				d = p.data and
				(let sendPair = (send->p) |
					(let sendData = (send -> d) |
						(((s.replyNum[send] != s.lastSentNum[send])=> (sendData in s.lastSent)) and
						((s.replyNum[send] = s.lastSentNum[send]) => (sendData in s.senders)) and
						#s.replyBuffer = 0 and
						sendData !in s'.senders and
						sendData in s'.lastSent and
						#s.buffer = 0 and
						s'.senders = s.senders - sendData and
						s.receivers = s'.receivers and
						s'.lastPacket = (s.lastPacket - (send->s.lastPacket[send]) + sendPair) and
						s'.lastSent = (s.lastSent) - (send->s.lastSent[send]) + sendData and
						s.replies = s'.replies and
						s.replyBuffer = s'.replyBuffer and
						s.lastReceivedNum = s'.lastReceivedNum and
						s.replyNum = s'.replyNum and
						s'.sent = s.sent + p and
						s'.lastSentNum = (send->(SequenceNumber - send.(s.lastSentNum)))  and
						(p.ErrorCheck[] => ((s'.buffer = s.buffer) or (s'.buffer = s.buffer + sendPair))) and
						(!p.ErrorCheck[] => (s'.buffer = s.buffer + sendPair))))))))
}

pred CanReceivePacket[s:State]{
	(one send:Sender | 
		(one p:Packet |
			(one d:(Data - ACK) |
				(one r: Receiver|
				d = p.data and
				(let receiveData = (r -> d) |
					(#s.replyBuffer = 0) and
					(s.buffer[send] = p) and
					(send.receiver = r) and
					receiveData !in s.receivers)))))
}

pred ReceivePacket[s,s':State]{
	s.type = ReceiveState and
	CanReceivePacket[s] and
	(one send:Sender | 
		(one p:Packet |
			(one d:(Data - (ACK)) |
				(one r: Receiver|
				d = p.data and
					(let sendPair = (send->p) |
						(let receiveData = (r -> d) |
							((one rep:Packet |
								rep.data = ACK and
								(p.ErrorCheck[] => rep.seqNum = p.seqNum) and
								(!p.ErrorCheck[] => rep.seqNum = s.lastReceivedNum[r]) and
								(rep !in s.sent) and
								(rep.ErrorCheck[] => (s'.replyBuffer = s.replyBuffer or s'.replyBuffer = s.replyBuffer + (r->rep))) and
								(!rep.ErrorCheck[] => (s'.replyBuffer = s.replyBuffer + (r->rep)))) and
							(#s.replyBuffer = 0) and
							(#s'.buffer = 0) and
							(s.buffer[send] = p) and
							(send.receiver = r) and
							s'.lastReceivedNum = (r->p.seqNum) and
							s'.buffer = s.buffer - sendPair and
							((p.ErrorCheck[]) => s'.receivers = s.receivers + receiveData) and
							((!p.ErrorCheck[]) => s.receivers = s'.receivers) and
							receiveData !in s.receivers and
							s.lastSent = s'.lastSent and
							s'.receivers - receiveData = s.receivers and
							s.replyNum = s'.replyNum and
							s.sent = s'.sent and
							s.replies = s'.replies and
							s.lastSentNum = s'.lastSentNum and
							s.lastPacket = s'.lastPacket and
							s.senders = s'.senders)))))))
}

pred CanReceiveReply[s:State]{
	(one r:Receiver|
		(one d:(ACK)|
			(one p:(Packet - s.sent) |
				p.data = d and
				(r->p) in s.replyBuffer)))
}

pred ReceiveReply[s,s':State]{
	s.type = ReceiveReplyState and
	CanReceiveReply[s] and
	(one r:Receiver|
		(one d:(ACK)|
			(one p:Packet |
				p.data = d and
				p in s'.sent and
				(one send:Sender|
					send = r.sender and
					(send->ACK) in s'.replies and
					(p.ErrorCheck[] => s'.replyNum = (send->p.seqNum)) and
					(!p.ErrorCheck[] => s'.replyNum = (send->s.lastSentNum[send])) and
					s.lastSent = s'.lastSent and
					s.receivers = s'.receivers and
					s.replies = s'.replies and
					s.buffer = s'.buffer and
					s.senders = s'.senders and
					s.sent = s'.sent - p and
					s.lastReceivedNum = s'.lastReceivedNum and
					s.lastSentNum = s'.lastSentNum and
					s'.replyNum = (s.replyNum - (send->(s.replyNum[send]))) + (send->p.seqNum) and
					(r->p) in s.replyBuffer and
					s.lastPacket = s'.lastPacket and
					s'.replyBuffer = s.replyBuffer - (r->p)))))
}

pred Packet.ErrorCheck{
	this.checksum != CorruptChecksum
}

pred State.Done[]{
	all d:(Data - (ACK)) | d in Receiver.(this.receivers)
}

pred State.Init[]{
	#this.receivers = 0 and #this.buffer = 0  and #this.replyBuffer = 0 and #this.lastSent = 0 and this.replies = {Sender->ACK}
	and (all s:Sender | (s->ACK) !in this.senders and (s->Seq0) in this.lastSentNum and (s-> Seq0 in this.replyNum))
	and this.sent = none and #this.lastReceivedNum = 0 and #this.senders > 0  and this.type = SendState and #this.lastPacket = 0
	and (all d:(Data - ACK) | one s:Sender | (s->d) in this.senders)
}

pred Transition[s, s':State]{
	(SendPacket[s, s'] or 
	ReceivePacket[s, s'] or
	ReceiveReply[s, s'] or
	ReSendPacket[s, s'])
}

pred TypeTransition[s, s':State]{
	(
		(
			(s.type = ReceiveReplyState and CanReceiveReply[s]) => s'.type = SendState
		) and
		(
			(s.type = ReceiveState and CanReceivePacket[s]) => s'.type = ReceiveReplyState
		) and
		(
			(s.type = SendState and CanSendPacket[s]) => s'.type = ReceiveState
		) and
		(
			(s.type = DeadState) => s'.type = ReceiveState
		) and
		(
			(
				(s.type = SendState and !CanReceivePacket[s']) or
				(s.type = ReceiveState and !CanReceiveReply[s']) or	
				(s.type = ReceiveReplyState and !CanSendPacket[s'])
			) => s'.type = DeadState
		)
	)
}

fact{
	receiver = ~sender
}

fact{
	all d:Data | some p:Packet | p.data = d and p.checksum != CorruptChecksum
}

fact{
	some p:Packet | p.checksum = CorruptChecksum
}

fact{
	(no d:Data | (some r:Receiver | (some r2:Receiver - r | (r->d) in State.receivers and (r2->d) in State.receivers))
		or (some s:Sender| (some s2:Sender -s | ((s->d) in State.senders and (s2->d) in State.senders)
			or ((s->d) in State.lastSent and (s2->d) in State.lastSent)
			or (some p:Packet | p.data = d and ((s->p) in State.buffer and (s2->p) in State.buffer)))))
}

fact{
	(all st:State | no d:Data | (d in Sender.(st.senders) and d in Receiver.(st.receivers))
		or (d in Sender.(st.senders) and d in (Sender.(st.buffer)).data)
		or (d in (Sender.(st.buffer)).data and d in Receiver.(st.receivers))) 
}

assert AlwaysWorks{
	(first.Init[] and
		all s:State - last |
			let s' = s.next |
				TypeTransition[s, s'] and Transition[s, s']) =>
					last.Done[]
}

pred Trace[]{
	(first.Init[] and
		all s:State - last |
			let s' = s.next |
				TypeTransition[s, s'] and Transition[s, s']) and last.Done[]
}

pred FirstWorks{
	first.Init[] and SendPacket[first, first.next]
}

pred show{}
check AlwaysWorks for 1 but exactly 9 State, exactly 6 Packet, exactly 3 Data, exactly 2 Checksum
run Trace for 1 but exactly 9 State, exactly 6 Packet, exactly 3 Data, exactly 2 Checksum, exactly 4 StateType
run show for 1 but exactly 10 State, exactly 6 Packet, exactly 3 Data, exactly 2 Checksum, exactly 4 StateType
run Init for 1 but exactly 1 State, exactly 6 Packet, exactly 3 Data, exactly 2 Checksum
run SendPacket for 1 but exactly 2 State, exactly 6 Packet, exactly 3 Data, exactly 2 Checksum, exactly 4 StateType
run FirstWorks for 1 but exactly 2 State, exactly 6 Packet, exactly 3 Data, exactly 2 Checksum, exactly 4 StateType

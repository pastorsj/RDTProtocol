module RDT10

sig State{}
abstract sig Machine{
	initState: one State
	states: set State
}

one sig Sender, Receiver extends Machine{}

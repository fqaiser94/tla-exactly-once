---- MODULE ExactlyOnce ----

EXTENDS Sequences, Integers

CONSTANT NULL

VARIABLES InputTopic, Buffer, OutputTopic, CommittedConsumerOffset, PC

vars == <<InputTopic, Buffer, OutputTopic, CommittedConsumerOffset, PC>>

Processes == {1, 2}

Init ==
    /\ InputTopic = <<1>>
    /\ Buffer = [ process \in Processes |-> NULL ]
    /\ OutputTopic = <<>>
    /\ CommittedConsumerOffset = 1
    /\ PC = [ process \in Processes |-> "Consume" ]

MessagesAvailable == CommittedConsumerOffset < Len(InputTopic) + 1

Update(function, x, y) == [ function EXCEPT ![x] = y ]

Consume(process) ==
    /\ PC[process] = "Consume"
    /\ IF MessagesAvailable
       THEN /\ Buffer' = Update(Buffer, process, InputTopic[CommittedConsumerOffset])
            /\ PC' = Update(PC, process, "ProduceCommit")
       ELSE /\ Buffer' = Update(Buffer, process, NULL)
            /\ PC' = Update(PC, process, "Done")
    /\ UNCHANGED <<InputTopic, OutputTopic, CommittedConsumerOffset>>

ProduceCommit(process) ==
    /\ PC[process] = "ProduceCommit"
    /\ OutputTopic' = Append(OutputTopic, Buffer[process])
    /\ CommittedConsumerOffset' = Buffer[process] + 1
    /\ PC' = Update(PC, process, "Consume")
    /\ UNCHANGED <<InputTopic, Buffer>>

Done(process) ==
    /\ PC[process] = "Done"
    /\ UNCHANGED vars

Restart(process) ==
    /\ PC[process] /= "Done"
    /\ Buffer' = Update(Buffer, process, NULL)
    /\ PC' = Update(PC, process, "Consume")
    /\ UNCHANGED <<InputTopic, OutputTopic, CommittedConsumerOffset>>

Next ==
    \E process \in Processes:
        \/ Consume(process)
        \/ ProduceCommit(process)
        \/ Restart(process)
        \/ Done(process)

Fairness ==
    \E process \in Processes:
        /\ WF_vars(Next)
        /\ SF_vars(ProduceCommit(process))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

Termination == <>[](\A process \in Processes: PC[process] = "Done")

NoDuplicatesIn(seq) ==
    \A i, j \in 1..Len(seq):
        i /= j => seq[i] /= seq[j]

NoDuplicates == NoDuplicatesIn(OutputTopic)

SeqContains(seq, value) ==
    \E x \in 1..Len(seq):
        seq[x] = value

SeqContainsAll(seq, values) ==
    \A i \in 1..Len(values):
        SeqContains(seq, values[i])

NoMissingData == <>[](SeqContainsAll(OutputTopic, InputTopic))

====

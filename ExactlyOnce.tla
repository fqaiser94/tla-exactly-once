---- MODULE ExactlyOnce ----

EXTENDS Sequences, Integers

CONSTANT NULL

VARIABLES InputTopic, Buffer, OutputTopic, CommittedConsumerOffset

vars == <<InputTopic, Buffer, OutputTopic, CommittedConsumerOffset>>

Init ==
    /\ InputTopic = <<1>>
    /\ Buffer = NULL
    /\ OutputTopic = <<>>
    /\ CommittedConsumerOffset = 1

MessagesAvailable == CommittedConsumerOffset < Len(InputTopic) + 1

ConsumeProduceCommit ==
    /\ MessagesAvailable
    /\ Buffer' = InputTopic[CommittedConsumerOffset]
    /\ OutputTopic' = Append(OutputTopic, Buffer')
    /\ CommittedConsumerOffset' = Buffer' + 1
    /\ UNCHANGED InputTopic

Done ==
    /\ ~MessagesAvailable
    /\ UNCHANGED vars

Next ==
    \/ ConsumeProduceCommit
    \/ Done

Fairness == WF_vars(Next)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

Termination == <>[](~MessagesAvailable)

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

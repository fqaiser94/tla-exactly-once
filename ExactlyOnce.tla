---- MODULE ExactlyOnce ----

EXTENDS Sequences, Integers

CONSTANT NULL

VARIABLES InputTopic, Buffer, OutputTopic, CommittedConsumerOffset, PC

vars == <<InputTopic, Buffer, OutputTopic, CommittedConsumerOffset, PC>>

Init ==
    /\ InputTopic = <<1>>
    /\ Buffer = NULL
    /\ OutputTopic = <<>>
    /\ CommittedConsumerOffset = 1
    /\ PC = "Consume"

MessagesAvailable == CommittedConsumerOffset < Len(InputTopic) + 1

Consume ==
    /\ PC = "Consume"
    /\ IF MessagesAvailable
       THEN /\ Buffer' = InputTopic[CommittedConsumerOffset]
            /\ PC' = "Produce"
       ELSE /\ Buffer' = NULL
            /\ PC' = "Done"
    /\ UNCHANGED <<InputTopic, OutputTopic, CommittedConsumerOffset>>

Produce ==
    /\ PC = "Produce"
    /\ OutputTopic' = Append(OutputTopic, Buffer)
    /\ PC' = "Commit"
    /\ UNCHANGED <<InputTopic, Buffer, CommittedConsumerOffset>>

Commit ==
    /\ PC = "Commit"
    /\ CommittedConsumerOffset' = Buffer + 1
    /\ PC' = "Consume"
    /\ UNCHANGED <<InputTopic, Buffer, OutputTopic>>

Done ==
    /\ PC = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Consume
    \/ Produce
    \/ Commit
    \/ Done

Fairness == WF_vars(Next)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

Termination == <>[](PC = "Done")

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

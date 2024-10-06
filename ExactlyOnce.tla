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
            /\ PC' = "ProduceCommit"
       ELSE /\ Buffer' = NULL
            /\ PC' = "Done"
    /\ UNCHANGED <<InputTopic, OutputTopic, CommittedConsumerOffset>>

ProduceCommit ==
    /\ PC = "ProduceCommit"
    /\ OutputTopic' = Append(OutputTopic, Buffer)
    /\ CommittedConsumerOffset' = Buffer + 1
    /\ PC' = "Consume"
    /\ UNCHANGED <<InputTopic, Buffer>>

Done ==
    /\ PC = "Done"
    /\ UNCHANGED vars

Restart ==
    /\ PC /= "Done"
    /\ Buffer' = NULL
    /\ PC' = "Consume"
    /\ UNCHANGED <<InputTopic, OutputTopic, CommittedConsumerOffset>>

Next ==
    \/ Consume
    \/ ProduceCommit
    \/ Done
    \/ Restart

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

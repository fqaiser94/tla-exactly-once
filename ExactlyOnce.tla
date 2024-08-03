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

Next == ConsumeProduceCommit

Spec ==
    /\ Init
    /\ [][Next]_vars

====

# sw-spi-cam-model

This repository is for the formal model and verification of the SPI driver with a camera.

## Related documents
1. Google document for discussions on related work: https://docs.google.com/document/d/1xOwqRDv1WGwzax5KOAUY40DR_kuldwy8KPgmYwXBlrw/edit?usp=sharing

2. AM335x Technical Reference Manual: https://www.ti.com/lit/ug/spruh73q/spruh73q.pdf

## Problems
Problem 1: for tx and rx automaton, there are 2 steps, channel_enabled and conf_ready. The problem is the order of two operations.

In the real hardware, I have tested both orders, enable first or conf first. Both can work, so the order does not matter for SPI bus. But in the model, in order to distinguish rx and tx that the CPU wants to perform, I set the conf first.

Problem 2: waht's the result of writing to a read-only(RO) SPI register.

Answer: 3 RO registers are included in this SPI model, SYSSTATUS, CH0STAT and RX0. After tests on the real hardware, the result showed that the write operations do not affect the SPI bus. In other words, writing to RO regs cannot lend the SPI model into an error state, just no changes of the SPI state.

# sw-spi-cam-model

This repository is for the formal model and verification of the SPI driver with a camera.

## Related documents
1. Google document for discussions on related work: https://docs.google.com/document/d/1xOwqRDv1WGwzax5KOAUY40DR_kuldwy8KPgmYwXBlrw/edit?usp=sharing

2. AM335x Technical Reference Manual: https://www.ti.com/lit/ug/spruh73q/spruh73q.pdf

## Problems
1. 2020.6.16 No error flags in the SPI registers: hard to model errors in the SPI TX/RX automaton, since no direct flags in SPI registers to indicate errors like overrun, see at am335x Manual Chapter 24 McSPI.

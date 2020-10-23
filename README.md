# sw-spi-cam-model

This repository is for the formal model and verification of the SPI driver with a camera.

### TODO
According to the driver and spi combined abstract model, there are 2 steps I think:

1. Remove interactions of spi and driver, in other words Write/Update, Read/Return.

2. Remove tau operations of spi and driver themselves.

Then, we can get a very abstract model to descride the spi behaviors, based on users view.

(TODO later, maybe not needed)

define an invariant for `spi`, for traces and functional correctness proof.

### Related documents
1. Google document for discussions on related work: https://docs.google.com/document/d/1xOwqRDv1WGwzax5KOAUY40DR_kuldwy8KPgmYwXBlrw/edit?usp=sharing

2. AM335x Technical Reference Manual: https://www.ti.com/lit/ug/spruh73q/spruh73q.pdf


# sw-spi-cam-model

This repository is for the formal model and verification of the SPI driver with a camera.

### TODO
1. The spi_model: add not_ready states to tx, rx and xfer automatons, as a way to synchronize auomatons. 

Change the init automaton, when init is done then others are ready, .

2. Apply above changes into the abstract model.

3. add spi.xfer.state ==> TX0 = buffer as a part of the ref_rel.

### Related documents
1. Google document for discussions on related work: https://docs.google.com/document/d/1xOwqRDv1WGwzax5KOAUY40DR_kuldwy8KPgmYwXBlrw/edit?usp=sharing

2. AM335x Technical Reference Manual: https://www.ti.com/lit/ug/spruh73q/spruh73q.pdf


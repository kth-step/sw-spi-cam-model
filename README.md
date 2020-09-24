# sw-spi-cam-model

This repository is for the formal model and verification of the SPI driver with a camera.

### TODO
Problem: The refinement model of SPI controller will have less states transtions, compared to the basic one. This would be a problem for the proof, since the states of ref model and basic model are not 1to1 corresponding.

Possible solution: add tau transition to ref model, like `s tau s`.

### Related documents
1. Google document for discussions on related work: https://docs.google.com/document/d/1xOwqRDv1WGwzax5KOAUY40DR_kuldwy8KPgmYwXBlrw/edit?usp=sharing

2. AM335x Technical Reference Manual: https://www.ti.com/lit/ug/spruh73q/spruh73q.pdf


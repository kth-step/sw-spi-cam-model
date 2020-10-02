# sw-spi-cam-model

This repository is for the formal model and verification of the SPI driver with a camera.

### TODO
1. use `spi_abs` as the abstract model name, rather than `spi_ref`.

2. define an invariant for `spi_abs`, mainly considering changed parts of tau transitions, in order to fulfill the refinement relation R.

3. define the refinement relation R for `spi_abs` and `spi`.

(TODO later)

4. use `update1 word32 word32` etc. for `spi_comb_tr`.

5. define an invariant for `spi`, for traces and functional correctness proof.

### Related documents
1. Google document for discussions on related work: https://docs.google.com/document/d/1xOwqRDv1WGwzax5KOAUY40DR_kuldwy8KPgmYwXBlrw/edit?usp=sharing

2. AM335x Technical Reference Manual: https://www.ti.com/lit/ug/spruh73q/spruh73q.pdf


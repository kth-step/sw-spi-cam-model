# sw-spi-cam-model

Refinement-Based Verification of Device-to-Device Information Flow

Definitions and proofs in HOL4

### Folder
- `spi_model`: definitions for SPI hardware model.
- `driver_model`: defines an SPI driver model.
- `ds_abs0`: the abstract model A.
- `ds_abs1`: the intermediate model B.
- `abs1_comb_thm`: weak bisimulation proofs for the SPI subsystem and the model B.
- `abs0_abs1_thm`: weak bisimulation proofs for the A and B models.
- `abs0_comb_thm`: weak bisimulation proofs for the SPI subsystem and the model A, proofs for correctness theorems and an invariant of model A.
- `cam_app`: a trivial camera model based on the model A as a device example.






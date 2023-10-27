# Goéland - Coq plugin first version

Goéland is an automated theorem prover using the tableau method for first order logic.

All the work shown in this repository is derived from the work of the team working on Goéland.

Please note that Goéland is licensed under the CeCILL 2.1 License.

### You can find the Goéland prover on [its dedicated GitHub repository](https://github.com/GoelandProver/Goeland).

## Authors
[Lorenzo PUCCIO](https://github.com/StOil-L)

## Context

This project was carried out during an internship at the LIRMM (*Laboratoire d'Informatique, de Robotique et de Microélectronique de Montpellier*), as part of the MAREL (Models and Reuse Engineering, Languages) team.

The aforementioned internship lasted between July 1st and September 1st, 2022.

This repository provides a limited version of Goéland for the purpose of demonstrating the first version of the prover's Coq plugin.

## Features

This version of Goéland allows the user to solve a [TPTP](https://tptp.org/) FOF problem file and produce a Coq proof file out of it.

The problem can be either order zero logic or first order logic.

The user can then manually solve the output Coq proof step-by-step with CoqIDE.

## Getting Started

### Prerequisites

As Goéland is developed and built for Linux, it is very difficult to natively run it on Windows.

Fortunately, a simple workaround for Windows exists in the form of the Windows Subsystem for Linux. I personally recommend installing WSL with the Ubuntu 22.04 LTS distribution using the following command line: `wsl.exe --install Ubuntu-22.04`. Follow the instructions displayed on your terminal to complete the installation of WSL.

Whether you wish to run Goéland with Linux or WSL, make sure to have the following packages installed:
- go (`sudo snap install go --classic`): version 1.18+
- goyacc (`sudo apt-get install golang-golang-x-tools`)
- make (`sudo apt install make`)
- coq-prover (`sudo snap install coq-prover`): version 8.6+

### Compilation & Usage

Upon cloning this repository, simply run the `make` command to compile the Goéland binaries into the newly created `_build` folder.

In order to solve a problem, run the following command line: `./_build/goeland -proof coq-demo/tptp/[PROBLEMNAME].p` where `[PROBLEMNAME]` is the name of a TPTP FOF problem file. (e.g. `pb2`)

The corresponding Coq proof file will be written in the `coq-demo/output/` folder. Launch CoqIDE and open the aforementioned file. You are now able to solve the TPTP problem manually.

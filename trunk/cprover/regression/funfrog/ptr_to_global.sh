#!/bin/bash

sed "s/( *PIRP Irp *,/(/g" |
sed "s/, *PIRP Irp *,/,/g" |
sed "s/, *PIRP Irp *)/)/g" |
sed "s/( *PIRP Irp *)/()/g" |
sed "s/^ *PIRP Irp *)/)/g" |
sed "s/if *( *Irp *)/if (1)/g" |
sed "s/( *Irp *,/(/g" |
sed "s/, *Irp *,/,/g" |
sed "s/, *Irp *)/)/g" |
sed "s/( *Irp *)/()/g" |
sed "s/if *( *pirp *)/if (1)/g" |
sed "s/( *pirp *,/(/g" |
sed "s/, *pirp *,/,/g" |
sed "s/, *pirp *)/)/g" |
sed "s/( *pirp *)/()/g" |
sed "s/, *currentIrp *)/)/g" |
sed "s/, *currentIrp *,/,/g" |
sed "s/( *currentIrp *,/(/g" |
sed "s/( *currentIrp *)/()/g" |
sed "s/pirp = &/girp = /g" |
sed "s/Irp->/girp\./g" |
sed "s/pirp->/girp\./g" |
sed "s/IRP *\* *pirp;//" |
sed "s/\(typedef struct _IRP IRP;\)/\1\nIRP girp;/"

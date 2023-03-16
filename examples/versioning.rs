extern crate riscv_target;

use riscv_target::Target0 as Target_2017;
use riscv_target::Target0 as Target_2019;
use riscv_target::{NamingJunk, Spec2017, Versioned};

fn main() {
    let t2017 = "riscv32imac-unknown-none-elf".parse::<Target_2017>();

    assert!(t2017.is_ok());
    assert_eq!(t2017.unwrap().to_string(), "riscv32imac-unknown-none-elf");

    let t2017_zicsr = "riscv32imacZicsr-unknown-none-elf".parse::<Target_2017>();
    assert!(t2017_zicsr.is_err());

    let t2019 = "riscv32imac-unknown-none-elf".parse::<Target_2019>();
    assert!(t2019.is_ok());
    assert_eq!(t2019.unwrap().to_string(), "riscv32imac-unknown-none-elf");

    let t2019_zicsr = "riscv32imacZicsr-unknown-none-elf".parse::<Target_2019>();
    assert!(t2019_zicsr.is_ok());
    assert_eq!(
        t2019_zicsr.unwrap().to_string(),
        "riscv32imacZicsr-unknown-none-elf"
    );

    // internal versioning is also a thing: maybe something like?
    type Foo = NamingJunk<Versioned<Spec2017>>;

    let _z = "RV64I1p0M1p0A1p0F1p0D1p0".parse::<Foo>();
    todo!("assertions?");
}

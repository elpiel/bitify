use bitify::{Error, FixedSize, Order};
use bitvec::prelude::BitSlice;
use std::convert::TryFrom;

/// example from wikipedia, orders the bits MSBit first!
/// @see https://en.wikipedia.org/wiki/ARINC_429#Word_format
fn main() {
    let builder = FixedSize::builder(32);

    // 0o203 = 0b1000_0011
    let input = [0o203, 0b0010_0010, 0b0011_0001, 0b1000_1001];

    println!(
        "Word: {}",
        input
            .iter()
            .map(|byte| { format!("{:08b}", byte) })
            .collect::<Vec<_>>()
            .join(" ")
    );

    // load the input and add the parity check (odd number of ones - 1)
    let (remaining, parser) = builder
        .load_sane(BitSlice::from_slice(&input), |bit_slice| {
            bit_slice.count_ones() % 2 != 0
        })
        .expect("Should load bits we have exact number of bits in input");

    assert!(remaining.is_empty());

    match handler(parser) {
        Err(e) => println!("Error: {:?}", e),
        _ => {}
    };
}

fn handler(parser: FixedSize) -> Result<(), Error> {
    use Order::*;
    let label = parser.take_byte(MSBit)?;
    assert_eq!("203", format!("{:o}", label));

    let sdi: SDI = SDI::try_from(parser.take_bits::<u8>(MSBit, 2)?).expect("Should just work");

    if BAROMETRIC_SENSOR_SDI == sdi && BAROMETRIC_LABEL == label {
        println!("Label: {:o}", label);
        let data: u32 = parser.take_bits(MSBit, 18)?;
        let ssm: u8 = parser.take_bits(MSBit, 2)?;
        let parity: u8 = parser.take_bits(MSBit, 1)?;

        println!("SDI (2 bits): {:?}", sdi);
        println!("Data (18 bits): {:b}", data);
        println!("SSM (2 bits): {:?}", ssm);
        println!("Parity (1 bit): {:?}", parity)
    } else {
        println!("Not intended for us... Skip!")
    }

    Ok(())
}
static BAROMETRIC_LABEL: u8 = 0o203;
static BAROMETRIC_SENSOR_SDI: SDI = SDI::BarometricSensor;

#[derive(Debug, PartialEq, Eq)]
pub enum SDI {
    BarometricSensor, // 00
    Second,           // 01
    Third,            // 10
    Fourth,           // 11
}

impl TryFrom<u8> for SDI {
    type Error = Error;
    fn try_from(from: u8) -> std::result::Result<Self, Self::Error> {
        let sdi = match from {
            0 => SDI::BarometricSensor,
            1 => SDI::Second,
            2 => SDI::Third,
            3 => SDI::Fourth,
            _ => return Err(Error::OutOfBound),
        };

        Ok(sdi)
    }
}

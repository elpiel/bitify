#![deny(clippy::all)]
use bitvec::prelude::*;
use std::cell::RefCell;

pub type Result<O> = std::result::Result<O, Error>;

#[derive(Debug, PartialEq, Eq)]
pub enum Needed {
    /// needs more data, but we do not know how much
    // Unknown,
    /// contains the required data size
    Size(usize),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Incomplete(Needed),
}

#[derive(Debug)]
pub enum Order {
    MSBit,
    LSBit,
}

#[derive(Debug)]
pub struct FixedSize {
    data: RefCell<BitVec<Msb0, u8>>,
    size: usize,
}

pub struct Builder {
    size: usize,
}

impl Builder {
    pub fn load(&self, input: &BitSlice<Msb0, u8>) -> Result<(BitVec<Msb0, u8>, FixedSize)> {
        let bitvec = BitVec::from(input);

        // if size > passed input, we need to fail!
        match self.size.checked_sub(bitvec.len()) {
            Some(needed) if needed > 0 => return Err(Error::Incomplete(Needed::Size(needed))),
            _ => {}
        };

        let (fixed_size_data, remaining) = bitvec.split_at(self.size);

        let fixed_size = FixedSize {
            size: self.size,
            data: RefCell::new(fixed_size_data.to_owned()),
        };
        Ok((remaining.to_vec(), fixed_size))
    }
}

impl FixedSize {
    #[allow(clippy::new_ret_no_self)]
    pub fn new(size: usize) -> Builder {
        Builder { size }
    }

    // @IDEA: Create a `fn drain`

    pub fn take_byte(&self, order: Order) -> Result<u8> {
        // if 8 bits > data length, we need to fail!
        match 8_usize.checked_sub(self.data.borrow().len()) {
            Some(needed) if needed > 0 => return Err(Error::Incomplete(Needed::Size(needed))),
            _ => {}
        };

        let mut data = self.data.borrow_mut();
        let drain = data.drain(0..8);

        // we need to collect it into a BitVec. since Drain doesn't impl BitField
        let byte = match order {
            Order::MSBit => {
                let bitvec = drain.collect::<BitVec<Msb0, u8>>();
                bitvec.load_be::<u8>()
            }
            Order::LSBit => {
                let bitvec = drain.collect::<BitVec<Lsb0, u8>>();

                bitvec.load_be::<u8>()
            }
        };

        Ok(byte)
    }

    pub fn take_bytes(&self, order: Order, bytes: u8) -> Result<Vec<u8>> {
        // MAX value is 2040 which is way less than a usize
        let bits_count: usize = usize::from(bytes) * 8;
        // @TODO: Own error! This returns how many Bits are still needed, this is not enough verbose
        // if 8 bits * num of bytes > data length, we need to fail!
        match bits_count.checked_sub(self.data.borrow().len()) {
            Some(needed) if needed > 0 => return Err(Error::Incomplete(Needed::Size(needed))),
            _ => {}
        };

        let mut data = self.data.borrow_mut();
        let drain = data.drain(0..bits_count);

        // we need to collect it into a BitVec. since Drain doesn't impl BitField
        let bytes = match order {
            Order::MSBit => drain.collect::<BitVec<Msb0, u8>>().into(),
            // @TODO:check if this is correct for both Big-endian and Little-endian
            Order::LSBit => drain.rev().collect::<BitVec<Msb0, u8>>().into(),
        };

        Ok(bytes)
    }

    pub fn take_bit<T: BitStore>(&self) -> Result<T> {
        match 1_usize.checked_sub(self.data.borrow().len()) {
            Some(needed) if needed > 0 => return Err(Error::Incomplete(Needed::Size(needed))),
            _ => {}
        };

        let bit: BitVec<Msb0, u8> = self.data.borrow_mut().drain(0..1).collect();
        Ok(bit.load_be::<T>())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn create_fixed_size_builder() {
        let builder = FixedSize::new(32);

        assert_eq!(32, builder.size);
    }

    #[test]
    fn builder_load_more_than_size_should_succeed() {
        let builder = FixedSize::new(32);
        let bitvec = bitvec![Msb0, u8; 1; 33];

        let (remaining, fixed_size) = builder
            .load(bitvec.as_bitslice())
            .expect("Should succeed when we have >= size input");

        assert_eq!(bitvec![Msb0, u8; 1], remaining);
        assert_eq!(bitvec![Msb0, u8; 1; 32], *fixed_size.data.borrow());
        assert_ne!(bitvec![Msb0, u8; 0; 32], *fixed_size.data.borrow());
    }

    #[test]
    fn builder_load_exact_size_should_succeed() {
        let builder = FixedSize::new(32);
        let bitvec = bitvec![Msb0, u8; 1; 32];

        let (remaining, fixed_size) = builder
            .load(bitvec.as_bitslice())
            .expect("Should succeed when we have >= size input");

        assert!(remaining.is_empty());
        assert_eq!(32, fixed_size.data.borrow().len());
    }

    #[test]
    fn builder_fails_to_load_since_it_needs_more_bits() {
        let builder = FixedSize::new(32);
        let bitvec = bitvec![Msb0, u8; 1; 10];

        let incomplete_err = builder
            .load(bitvec.as_bitslice())
            .expect_err("Should fail as we are passing less bits than needed");

        assert_ne!(Error::Incomplete(Needed::Size(10)), incomplete_err);
        assert_eq!(Error::Incomplete(Needed::Size(22)), incomplete_err);
    }

    #[test]
    fn fixed_size_should_load_a_byte_in_msbit() {
        let byte = 176_u8;
        let mut bitvec: BitVec<Msb0, u8> = BitVec::from_element(byte);
        bitvec.push(true);
        bitvec.push(false);

        let builder = FixedSize::new(10);
        let (remaining, fixed_size) = builder.load(&bitvec).expect("We should have 10 bits now");

        assert!(remaining.is_empty());
        let actual_byte = fixed_size
            .take_byte(Order::MSBit)
            .expect("We should have 1 byte + 2 bits");

        assert_eq!(byte, actual_byte);

        assert_eq!(bitvec![Msb0, u8; 1, 0], *fixed_size.data.borrow());
    }

    #[test]
    fn fixed_size_should_load_a_byte_in_lsbit() {
        let byte = 176_u8;
        let mut bitvec: BitVec<Msb0, u8> = BitVec::from_element(byte);
        bitvec.push(true);
        bitvec.push(false);

        let builder = FixedSize::new(10);
        let (remaining, fixed_size) = builder.load(&bitvec).expect("We should have 10 bits now");

        assert!(remaining.is_empty());
        let actual_byte = fixed_size
            .take_byte(Order::LSBit)
            .expect("We should have 1 byte + 2 bits");

        assert_eq!(byte.reverse_bits(), actual_byte);

        assert_eq!(bitvec![Msb0, u8; 1, 0], *fixed_size.data.borrow());
    }

    #[test]
    fn fixed_size_should_load_multiple_bytes_and_bits_in_msbit() {
        let mut bitvec: BitVec<Msb0, u8> = bitvec![Msb0, u8; 0];
        let bytes: [u8; 2] = [201, 176];
        bitvec.append(&mut BitVec::<Msb0, u8>::from_slice(&bytes));
        bitvec.push(true);

        let builder = FixedSize::new(18);
        let (remaining, fixed_size) = builder
            .load(&bitvec)
            .expect("We should have exactly 18 bits inside");

        assert_eq!(0, remaining.len());

        let first_bit = fixed_size.take_bit::<u8>().expect("should have 1 bit");
        assert_eq!(0, first_bit);

        let actual_bytes = fixed_size
            .take_bytes(Order::MSBit, 2)
            .expect("we should have 2 bytes + 2 bits");

        assert_eq!(bytes.to_vec(), actual_bytes);

        let last_bit = fixed_size.take_bit::<u8>().expect("should have 1 bit");
        assert_eq!(1, last_bit);
    }

    #[test]
    fn fixed_size_should_load_multiple_bytes_and_bits_in_lsbit() {
        let mut bitvec: BitVec<Msb0, u8> = bitvec![Msb0, u8; 0];
        let bytes: [u8; 2] = [201, 176];
        bitvec.append(&mut BitVec::<Msb0, u8>::from_slice(&bytes));
        bitvec.push(true);

        let builder = FixedSize::new(18);
        let (remaining, fixed_size) = builder
            .load(&bitvec)
            .expect("We should have exactly 18 bits inside");

        assert_eq!(0, remaining.len());

        let first_bit = fixed_size.take_bit::<u8>().expect("should have 1 bit");
        assert_eq!(0, first_bit);

        let actual_bytes = fixed_size
            .take_bytes(Order::LSBit, 2)
            .expect("we should have 2 bytes + 2 bits");

        // we should get a reversed order of both - bytes and bits
        assert_eq!(
            [176_u8.reverse_bits(), 201_u8.reverse_bits()].to_vec(),
            actual_bytes
        );

        let last_bit = fixed_size.take_bit::<u8>().expect("should have 1 bit");
        assert_eq!(1, last_bit);
    }
}

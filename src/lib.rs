use bitvec::prelude::*;
use nom::{error::ErrorKind, Err as NomErr, IResult, Needed};
use std::cell::RefCell;

pub type BResult<O> = Result<O, NomErr<ErrorKind>>;

#[derive(Debug)]
pub struct FixedSize {
    data: RefCell<BitVec<Msb0, u8>>,
    size: usize,
}

pub struct Builder {
    size: usize,
}

impl Builder {
    pub fn load(&self, input: &BitSlice<Msb0, u8>) -> IResult<BitVec<Msb0, u8>, FixedSize> {
        let bitvec = BitVec::from(input);

        // if size > passed input, we need to fail!
        match self.size.checked_sub(bitvec.len()) {
            Some(needed) if needed > 0 => return Err(NomErr::Incomplete(Needed::Size(needed))),
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
    pub fn new(size: usize) -> Builder {
        Builder { size }
    }

    // @IDEA: Create a `fn drain`

    pub fn take_byte(&self) -> BResult<u8> {
        // @TODO: Own error! This returns how many Bits are still needed, this is not enough verbose
        // if 8 bits > data length, we need to fail!
        match 8_usize.checked_sub(self.data.borrow().len()) {
            Some(needed) if needed > 0 => return Err(NomErr::Incomplete(Needed::Size(needed))),
            _ => {}
        };

        // we need to collect it into a BitVec. since Drain doesn impl BitField
        let bitvec: BitVec<Msb0, u8> = self.data.borrow_mut().drain(0..8).collect();

        Ok(bitvec.load_be::<u8>())
    }

    pub fn take_bytes(&self, bytes: u8) -> BResult<Vec<u8>> {
        // MAX value is 2040 which is way less than a usize
        let bits_count: usize = usize::from(bytes) * 8;
        // @TODO: Own error! This returns how many Bits are still needed, this is not enough verbose
        // if 8 bits * num of bytes > data length, we need to fail!
        match bits_count.checked_sub(self.data.borrow().len()) {
            Some(needed) if needed > 0 => return Err(NomErr::Incomplete(Needed::Size(needed))),
            _ => {}
        };

        // we need to collect it into a BitVec. since Drain doesn impl BitField
        let bitvec: BitVec<Msb0, u8> = self.data.borrow_mut().drain(0..bits_count).collect();

        Ok(bitvec.into_vec())
    }

    pub fn take_bit<O: BitStore>(&self) -> BResult<O> {
        match 1_usize.checked_sub(self.data.borrow().len()) {
            Some(needed) if needed > 0 => return Err(NomErr::Incomplete(Needed::Size(needed))),
            _ => {}
        };

        let bit: BitVec<Msb0, u8> = self.data.borrow_mut().drain(0..1).collect();
        Ok(bit.load_be::<O>())
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

        assert_ne!(NomErr::Incomplete(Needed::Size(10)), incomplete_err);
        assert_eq!(NomErr::Incomplete(Needed::Size(22)), incomplete_err);
    }

    #[test]
    fn fixed_size_should_load_a_byte() {
        let byte = 176_u8;
        let mut bitvec: BitVec<Msb0, u8> = BitVec::from_element(byte);
        bitvec.push(true);
        bitvec.push(false);

        let builder = FixedSize::new(10);
        let (remaining, fixed_size) = builder.load(&bitvec).expect("We should have 10 bits now");

        assert!(remaining.is_empty());
        
        let actual_byte = fixed_size
            .take_byte()
            .expect("We should have 1 byte + 2 bits");

        assert_eq!(byte, actual_byte);

        assert_eq!(bitvec![Msb0, u8; 1, 0], *fixed_size.data.borrow());
    }

    #[test]
    fn fixed_size_should_load_multiple_bytes_and_bits() {
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
            .take_bytes(2)
            .expect("we should have 2 bytes + 2 bits");

        assert_eq!(bytes.to_vec(), actual_bytes);

        let last_bit = fixed_size.take_bit::<u8>().expect("should have 1 bit");
        assert_eq!(1, last_bit);
    }
}

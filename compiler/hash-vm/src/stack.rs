pub struct Stack {
    data: Vec<u8>,
}

impl Stack {
    pub fn new(size: usize) -> Self {
        Stack {
            data: Vec::with_capacity(size),
        }
    }

    pub fn pop8(&self) -> &[u8; 1] {
        todo!()
    }

    pub fn pop16(&self) -> &[u8; 2] {
        todo!()
    }

    pub fn pop32(&self) -> &[u8; 4] {
        todo!()
    }

    pub fn pop64(&self) -> &[u8; 8] {
        todo!()
    }

    pub fn push8(&self, value: &[u8; 1]) {
        todo!()
    }

    pub fn push16(&self, value: &[u8; 2]) {
        todo!()
    }

    pub fn push32(&self, value: &[u8; 4]) {
        todo!()
    }

    pub fn push64(&self, value: &[u8; 8]) {
        todo!()
    }
}

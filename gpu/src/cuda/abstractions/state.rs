use super::errors::CudaError;
use cudarc::{
    driver::{safe::CudaSlice, CudaDevice, CudaFunction, DeviceRepr},
    nvrtc::safe::Ptx,
};
use std::sync::Arc;

const STARK256_PTX: &str = include_str!("../../../../math/src/gpu/cuda/shaders/field/stark256.ptx");

/// Structure for abstracting basic calls to a CUDA device and saving the state. Used for
/// implementing GPU parallel computations in CUDA.
pub struct CudaState {
    device: Arc<CudaDevice>,
}

impl CudaState {
    /// Creates a new CUDA state with the first GPU.
    pub fn new() -> Result<Self, CudaError> {
        let device =
            CudaDevice::new(0).map_err(|err| CudaError::DeviceNotFound(err.to_string()))?;
        let state = Self { device };

        // Load PTX libraries
        state.load_library(STARK256_PTX, "stark256")?;

        Ok(state)
    }

    pub fn load_library<F: IsFFTField>(&self, src: &'static str) -> Result<(), CudaError> {
        let mod_name: &'static str = F::field_name();
        let functions = [
            "radix2_dit_butterfly",
            "calc_twiddles",
            "calc_twiddles_bitrev",
            "bitrev_permutation",
        ];
        self.device
            .load_ptx(Ptx::from_src(src), mod_name, &functions)
            .map_err(|err| CudaError::PtxError(err.to_string()))
    }

    pub fn get_function(&self, mod_name: &str, func_name: &str) -> Result<CudaFunction, CudaError> {
        self.device
            .get_func(mod_name, func_name)
            .ok_or_else(|| CudaError::FunctionError(func_name.to_string()))
    }

    /// Allocates a buffer in the GPU and copies `data` into it. Returns its handle.
    pub fn alloc_buffer_with_data<T: DeviceRepr>(
        &self,
        data: &[T],
    ) -> Result<CudaSlice<T>, CudaError> {
        self.device
            .htod_sync_copy(data)
            .map_err(|err| CudaError::AllocateMemory(err.to_string()))
    }

    pub fn retrieve_result<T>(&self, src: CudaSlice<T>) -> Result<Vec<T>, CudaError>
    where
        T: Clone + Default + DeviceRepr + Unpin,
    {
        self.device
            .sync_reclaim(src)
            .map_err(|err| CudaError::RetrieveMemory(err.to_string()))
    }
}

pub(crate) struct CalcTwiddlesFunction<F: IsField> {
    device: Arc<CudaDevice>,
    function: CudaFunction,
    omega: CudaSlice<CUDAFieldElement<F>>,
    twiddles: CudaSlice<CUDAFieldElement<F>>,
}

impl<F: IsField> CalcTwiddlesFunction<F> {
    fn new(
        device: Arc<CudaDevice>,
        function: CudaFunction,
        omega: CudaSlice<CUDAFieldElement<F>>,
        twiddles: CudaSlice<CUDAFieldElement<F>>,
    ) -> Self {
        Self {
            device,
            function,
            omega,
            twiddles,
        }
    }

    pub(crate) fn launch(&mut self, group_size: usize) -> Result<(), CudaError> {
        let grid_dim = (1, 1, 1); // in blocks
        let block_dim = (group_size as u32, 1, 1);

        if block_dim.0 as usize > DeviceSlice::len(&self.twiddles) {
            return Err(CudaError::IndexOutOfBounds(
                block_dim.0 as usize,
                self.twiddles.len(),
            ));
        }

        let config = LaunchConfig {
            grid_dim,
            block_dim,
            shared_mem_bytes: 0,
        };
        // Launching kernels must be done in an unsafe block.
        // Calling a kernel is similar to calling a foreign-language function,
        // as the kernel itself could be written in C or unsafe Rust.
        unsafe {
            self.function
                .clone()
                .launch(config, (&mut self.twiddles, &self.omega))
        }
        .map_err(|err| CudaError::Launch(err.to_string()))
    }

    pub(crate) fn retrieve_result(self) -> Result<Vec<FieldElement<F>>, CudaError> {
        let Self {
            device, twiddles, ..
        } = self;
        let output = device
            .sync_reclaim(twiddles)
            .map_err(|err| CudaError::RetrieveMemory(err.to_string()))?
            .into_iter()
            .map(FieldElement::from)
            .collect();

        Ok(output)
    }
}

pub(crate) struct BitrevPermutationFunction<F: IsField> {
    device: Arc<CudaDevice>,
    function: CudaFunction,
    input: CudaSlice<CUDAFieldElement<F>>,
    result: CudaSlice<CUDAFieldElement<F>>,
}

impl<F: IsField> BitrevPermutationFunction<F> {
    fn new(
        device: Arc<CudaDevice>,
        function: CudaFunction,
        input: CudaSlice<CUDAFieldElement<F>>,
        result: CudaSlice<CUDAFieldElement<F>>,
    ) -> Self {
        Self {
            device,
            function,
            input,
            result,
        }
    }

    pub(crate) fn launch(&mut self, group_size: usize) -> Result<(), CudaError> {
        let grid_dim = (1, 1, 1); // in blocks
        let block_dim = (group_size as u32, 1, 1);

        if block_dim.0 as usize > DeviceSlice::len(&self.input) {
            return Err(CudaError::IndexOutOfBounds(
                block_dim.0 as usize,
                self.input.len(),
            ));
        } else if block_dim.0 as usize > DeviceSlice::len(&self.result) {
            return Err(CudaError::IndexOutOfBounds(
                block_dim.0 as usize,
                self.result.len(),
            ));
        }

        let config = LaunchConfig {
            grid_dim,
            block_dim,
            shared_mem_bytes: 0,
        };
        // Launching kernels must be done in an unsafe block.
        // Calling a kernel is similar to calling a foreign-language function,
        // as the kernel itself could be written in C or unsafe Rust.
        unsafe {
            self.function
                .clone()
                .launch(config, (&mut self.input, &self.result))
        }
        .map_err(|err| CudaError::Launch(err.to_string()))
    }

    pub(crate) fn retrieve_result(self) -> Result<Vec<FieldElement<F>>, CudaError> {
        let Self { device, result, .. } = self;
        let output = device
            .sync_reclaim(result)
            .map_err(|err| CudaError::RetrieveMemory(err.to_string()))?
            .into_iter()
            .map(FieldElement::from)
            .collect();

        Ok(output)
    }
}

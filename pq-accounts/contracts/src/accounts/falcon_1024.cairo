//! Falcon-1024 account contract.
//!
//! This account stores the packed 57-felt NTT-domain public key and validates a 116-felt
//! signature (the Falcon-512 hint layout at n = 1024) over the transaction hash, deriving the
//! message point with the standard SHAKE-256 hash-to-point of the Falcon specification, so any
//! standards-compliant Falcon signer (falcon.py, for one) produces valid signatures.

#[starknet::contract(account)]
pub mod Falcon1024Account {
    use pqbench_falcon_1024::Falcon1024Verifier;
    use crate::utils::account::PqAccountComponent;

    component!(path: PqAccountComponent, storage: account, event: AccountEvent);

    #[abi(embed_v0)]
    impl AccountImpl =
        PqAccountComponent::AccountImpl<ContractState, Falcon1024Verifier>;
    #[abi(embed_v0)]
    impl DeployableImpl =
        PqAccountComponent::DeployableImpl<ContractState, Falcon1024Verifier>;
    #[abi(embed_v0)]
    impl PublicKeyImpl = PqAccountComponent::PublicKeyImpl<ContractState>;

    impl InternalImpl = PqAccountComponent::InternalImpl<ContractState>;

    #[storage]
    struct Storage {
        #[substorage(v0)]
        account: PqAccountComponent::Storage,
    }

    #[event]
    #[derive(Drop, starknet::Event)]
    enum Event {
        #[flat]
        AccountEvent: PqAccountComponent::Event,
    }

    /// Initializes the account with the packed Falcon public key used for validation.
    #[constructor]
    fn constructor(ref self: ContractState, public_key: Array<felt252>) {
        self.account.initializer(public_key);
    }
}

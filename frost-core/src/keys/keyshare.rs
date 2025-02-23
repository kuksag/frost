//!
use alloc::collections::BTreeMap;

use crate::{compute_lagrange_coefficient, keys::dkg::{compute_proof_of_knowledge, round1, round2}, keys::{
    evaluate_polynomial, generate_coefficients, generate_secret_polynomial
    , validate_num_of_signers, PublicKeyPackage,
    SigningKey, SigningShare,
}, Ciphersuite, CryptoRng, Error, Field, Group, Header, Identifier, RngCore};

use super::{KeyPackage, SecretShare};
use crate::keys::dkg::verify_proof_of_knowledge;
use core::iter;

///
pub fn part1<C: Ciphersuite, R: RngCore + CryptoRng>(
    identifier: Identifier<C>,
    old_participants: Vec<Identifier<C>>,
    old_key_package: Option<SigningShare<C>>,
    max_signers: u16,
    min_signers: u16,
    mut rng: R,
) -> Result<(round1::SecretPackage<C>, round1::Package<C>), Error<C>> {
    validate_num_of_signers::<C>(min_signers, max_signers)?;

    let scalar = old_key_package
        .map(|key_package| {
            let identifiers = old_participants.iter().copied().collect();
            // Normalize participant's secret share, so that now holds `S = \sum s_i`
            let lagrange_coefficient =
                compute_lagrange_coefficient(&identifiers, None, identifier).unwrap();
            lagrange_coefficient * key_package.to_scalar()
        })
        .unwrap_or(<<C::Group as Group>::Field>::zero());

    // Ignoring `SigningKey::from_scalar` since it will fail on zero element. 
    let signing_key = SigningKey {
        scalar, 
    };

    // Round 1, Step 1
    let coefficients = generate_coefficients::<C, R>(min_signers as usize - 1, &mut rng);

    let (coefficients, commitment) =
        generate_secret_polynomial(&signing_key, max_signers, min_signers, coefficients)?;

    let proof_of_knowledge =
        compute_proof_of_knowledge(identifier, &coefficients, &commitment, &mut rng)?;

    let secret_package = round1::SecretPackage::new(
        identifier,
        coefficients.clone(),
        commitment.clone(),
        min_signers,
        max_signers,
    );
    let package = round1::Package {
        header: Header::default(),
        commitment,
        proof_of_knowledge,
    };

    Ok((secret_package, package))
}

///
pub fn part2<C: Ciphersuite>(
    secret_package: round1::SecretPackage<C>,
    round1_packages: &BTreeMap<Identifier<C>, round1::Package<C>>,
) -> Result<
    (
        round2::SecretPackage<C>,
        BTreeMap<Identifier<C>, round2::Package<C>>,
    ),
    Error<C>,
> {
    if round1_packages.len() != (secret_package.max_signers - 1) as usize {
        return Err(Error::IncorrectNumberOfPackages);
    };

    let mut round2_packages = BTreeMap::new();

    for (sender_identifier, round1_package) in round1_packages {
        if round1_package.commitment.0.len() != secret_package.min_signers as usize {
            return Err(Error::IncorrectNumberOfCommitments);
        }

        let ell = *sender_identifier;

        verify_proof_of_knowledge(
            ell,
            &round1_package.commitment,
            &round1_package.proof_of_knowledge,
        )?;

        // Round 2, Step 1
        //
        // > Each P_i securely sends to each other participant P_ℓ a secret share (ℓ, f_i(ℓ)),
        // > deleting f_i and each share afterward except for (i, f_i(i)),
        // > which they keep for themselves.
        let signing_share = SigningShare::from_coefficients(&secret_package.coefficients(), ell);

        round2_packages.insert(
            ell,
            round2::Package {
                header: Header::default(),
                signing_share,
            },
        );
    }
    let fii = evaluate_polynomial(secret_package.identifier, &secret_package.coefficients());

    Ok((
        round2::SecretPackage::new(
            secret_package.identifier,
            secret_package.commitment,
            fii,
            secret_package.min_signers,
            secret_package.max_signers,
        ),
        round2_packages,
    ))
}

///
pub fn part3<C: Ciphersuite>(
    round2_secret_package: &round2::SecretPackage<C>,
    round1_packages: &BTreeMap<Identifier<C>, round1::Package<C>>,
    round2_packages: &BTreeMap<Identifier<C>, round2::Package<C>>,
) -> Result<(KeyPackage<C>, PublicKeyPackage<C>), Error<C>> {
    if round1_packages.len() != (round2_secret_package.max_signers - 1) as usize {
        return Err(Error::IncorrectNumberOfPackages);
    }
    if round1_packages.len() != round2_packages.len() {
        return Err(Error::IncorrectNumberOfPackages);
    }
    if round1_packages
        .keys()
        .any(|id| !round2_packages.contains_key(id))
    {
        return Err(Error::IncorrectPackage);
    }

    let mut signing_share = <<C::Group as Group>::Field>::zero();

    for (sender_identifier, round2_package) in round2_packages {
        // Round 2, Step 2
        //
        // > Each P_i verifies their shares by calculating:
        // > g^{f_ℓ(i)} ≟ ∏^{t−1}_{k=0} φ^{i^k mod q}_{ℓk}, aborting if the
        // > check fails.
        let ell = *sender_identifier;
        let f_ell_i = round2_package.signing_share;

        let commitment = &round1_packages
            .get(&ell)
            .ok_or(Error::PackageNotFound)?
            .commitment;

        // The verification is exactly the same as the regular SecretShare verification;
        // however the required components are in different places.
        // Build a temporary SecretShare so what we can call verify().
        let secret_share = SecretShare {
            header: Header::default(),
            identifier: round2_secret_package.identifier,
            signing_share: f_ell_i,
            commitment: commitment.clone(),
        };

        // Verify the share. We don't need the result.
        let _ = secret_share.verify()?;

        // Round 2, Step 3
        //
        // > Each P_i calculates their long-lived private signing share by computing
        // > s_i = ∑^n_{ℓ=1} f_ℓ(i), stores s_i securely, and deletes each f_ℓ(i).
        signing_share = signing_share + f_ell_i.to_scalar();
    }

    signing_share = signing_share + round2_secret_package.secret_share();

    // Build new signing share
    let signing_share = SigningShare::new(signing_share);

    // Round 2, Step 4
    //
    // > Each P_i calculates their public verification share Y_i = g^{s_i}.
    let verifying_share = signing_share.into();

    let commitments: BTreeMap<_, _> = round1_packages
        .iter()
        .map(|(id, package)| (*id, &package.commitment))
        .chain(iter::once((
            round2_secret_package.identifier,
            &round2_secret_package.commitment,
        )))
        .collect();

    let public_key_package = PublicKeyPackage::from_dkg_commitments(&commitments)?;

    let key_package = KeyPackage {
        header: Header::default(),
        identifier: round2_secret_package.identifier,
        signing_share,
        verifying_share,
        verifying_key: public_key_package.verifying_key,
        min_signers: round2_secret_package.min_signers,
    };

    Ok((key_package, public_key_package))
}

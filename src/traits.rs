/* ************************************************************************** */
/*                                                                            */
/*                                                        :::      ::::::::   */
/*   traits.rs                                          :+:      :+:    :+:   */
/*                                                    +:+ +:+         +:+     */
/*   By: ggalon <ggalon@student.42lyon.fr>          +#+  +:+       +#+        */
/*                                                +#+#+#+#+#+   +#+           */
/*   Created: 2025/01/27 16:58:52 by ggalon            #+#    #+#             */
/*   Updated: 2025/01/27 17:26:04 by ggalon           ###   ########.fr       */
/*                                                                            */
/* ************************************************************************** */

use std::fmt::Debug;
use std::ops::{BitAnd, BitXor, Shl, Shr};

pub trait Traits:
	Debug +
	Default +
	Copy +
	PartialEq +
	BitAnd<Output = Self> +
	BitXor<Output = Self> +
	Shl<u32, Output = Self> +
	Shr<u32, Output = Self> {}


impl<K> Traits for K where
	K: Debug +
	Default +
	Copy +
	PartialEq +
	BitAnd<Output = K> +
	BitXor<Output = K> +
	Shl<u32, Output = K> +
	Shr<u32, Output = K> {}
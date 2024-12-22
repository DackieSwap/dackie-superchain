// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Predeploys} from '@contracts-bedrock/libraries/Predeploys.sol';
import {SuperchainERC20} from '@contracts-bedrock/L2/SuperchainERC20.sol';
import {Ownable} from '@solady/auth/Ownable.sol';

/// @title DackieSuperchain
/// @notice Implementation of a SuperchainERC20 token with minting and burning capabilities
/// @dev Extends SuperchainERC20 for cross-chain functionality and Ownable for access control
contract DackieSuperchain is SuperchainERC20, Ownable {
    // Token metadata storage
    string private _name;
    string private _symbol;
    uint8 private immutable _decimals;
    
    // Role addresses for minting control
    address public migrator;
    address public minter;
    
    // Maximum token supply (115 million)
    uint256 private constant MAX_SUPPLY = 115000000 * 10 ** 18;

    // Events for role changes and token operations
    event MigratorSet(address indexed oldMigrator, address indexed newMigrator);
    event MinterSet(address indexed oldMinter, address indexed newMinter);
    event Mint(address indexed to, uint256 amount);
    event Burn(address indexed from, uint256 amount);

    /// @notice Contract constructor
    /// @param owner_ Address that will own the contract
    /// @param name_ Token name
    /// @param symbol_ Token symbol
    /// @param decimals_ Number of decimals for token amounts
    constructor(
        address owner_,
        string memory name_,
        string memory symbol_,
        uint8 decimals_
    ) {
        require(owner_ != address(0), "Owner cannot be zero address");
        _name = name_;
        _symbol = symbol_;
        _decimals = decimals_;
        _initializeOwner(owner_);
    }

    /// @notice Returns the name of the token
    function name() public view virtual override returns (string memory) {
        return _name;
    }

    /// @notice Returns the symbol of the token
    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    /// @notice Returns the number of decimals used for token amounts
    function decimals() public view override returns (uint8) {
        return _decimals;
    }

    /// @notice Modifier to restrict functions to migrator or minter
    modifier onlyMigratorOrMinter() {
        require(
            msg.sender == migrator || msg.sender == minter,
            'Only migrator or minter can mint'
        );
        _;
    }

    /// @notice Mints new tokens to a specified address
    /// @param to_ Address to receive the minted tokens
    /// @param amount_ Amount of tokens to mint
    /// @dev Only callable by migrator or minter, respects max supply
    function mintTo(address to_, uint256 amount_) external onlyMigratorOrMinter {
        require(amount_ > 0, "Amount must be greater than 0");
        require(
            totalSupply() + amount_ <= MAX_SUPPLY,
            'Cannot mint: max supply reached'
        );
        _mint(to_, amount_);
        emit Mint(to_, amount_);
    }

    /// @notice Burns tokens from the caller's address
    /// @param amount_ Amount of tokens to burn
    function burn(uint256 amount_) external {
        require(amount_ > 0, "Amount must be greater than 0");
        require(
            balanceOf(msg.sender) >= amount_,
            "Insufficient balance to burn"
        );
        _burn(msg.sender, amount_);
        emit Burn(msg.sender, amount_);
    }

    /// @notice Sets a new migrator address
    /// @param newMigrator_ Address of the new migrator
    /// @dev Only callable by owner
    function setMigrator(address newMigrator_) external onlyOwner {
        address oldMigrator = migrator;
        require(newMigrator_ != oldMigrator, "New migrator must be different");
        migrator = newMigrator_;
        emit MigratorSet(oldMigrator, newMigrator_);
    }

    /// @notice Sets a new minter address
    /// @param newMinter_ Address of the new minter
    /// @dev Only callable by owner
    function setMinter(address newMinter_) external onlyOwner {
        address oldMinter = minter;
        require(newMinter_ != oldMinter, "New minter must be different");
        minter = newMinter_;
        emit MinterSet(oldMinter, newMinter_);
    }
}

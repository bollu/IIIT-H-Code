class User < ApplicationRecord
    attr_accessor :password_conformation
    validates :username, presence: true, uniqueness: true
    validates :password, presence: true, length: {minimum: 6}
    validates :email, presence: true
    validates :name, presence: true

    has_many :answered_surveys, foreign_key: "id", class_name: "Survey"
    def authenticate(given_password)
        return self.password == given_password
    end
end
